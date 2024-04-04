#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include "coordination.h"
#include <signal.h>

// Heartbeat timeout length
#define HB_TIMEOUT_LEN 5000 // 5 seconds for testing

// Hardcoded paths (ORDERED BY PRIORITY)
#define NUM_PATHS 4
// assume in node_id order, we have (Main ECU, Sub ECU, Main VCU, Sub VCU)
// then highest priority path is (Main ECU, Main VCU) or (0, 2) w/node_ids
struct path paths[NUM_PATHS] = {{0, 2}, {0, 3}, {1, 2}, {1, 3}};

/* GLOBAL DATA */
struct coordination_node this_node;
struct condition_variable election_status;
struct thread_pool tpool;

/* THREAD POOL FUNCTIONS */
int thread_pool_init(int count)
{
    tpool.threads = (pthread_t *)malloc(sizeof(pthread_t) * count);

    memset(tpool.threads, 0, sizeof(pthread_t) * count);
    tpool.total_count = count;
    tpool.num_allocated = 0;
    pthread_mutex_init(&tpool.mu, NULL);

    return 0;
}

int thread_pool_destroy()
{
    for (int i = 0; i < tpool.num_allocated; i++)
    {
        pthread_join(tpool.threads[i], NULL);
    }
    free(tpool.threads);
    return 0;
}

int thread_pool_resize() // double size of thread pool
{
    if (tpool.total_count == 0)
    {
        fprintf(stderr, "Error: thread pool is empty, cannot resize\n");
        return -1;
    }

    int new_count = tpool.total_count * 2;

    pthread_t *new_threads = (pthread_t *)malloc(sizeof(pthread_t) * new_count);
    if (new_threads == NULL)
    {
        fprintf(stderr, "Error: failed to allocate more threads\n");
        return -1;
    }

    memcpy(new_threads, tpool.threads, sizeof(pthread_t) * tpool.total_count);

    free(tpool.threads);

    tpool.total_count = new_count;
    tpool.threads = new_threads;

    return 0;
}

int thread_pool_assign_task(void *func, void *args)
{
    return pthread_create(get_thread(), NULL, func, args);
}

pthread_t *get_thread()
{
    pthread_mutex_lock(&tpool.mu);

    // if out of threads, make pool bigger
    if (tpool.num_allocated == tpool.total_count)
    {
        thread_pool_resize();
    }

    pthread_t *ret_thread = &tpool.threads[tpool.num_allocated++];

    pthread_mutex_unlock(&tpool.mu);
    return ret_thread;
}

pthread_t *get_threads(int count)
{
    pthread_mutex_lock(&tpool.mu);

    // if out of threads, make pool bigger
    while (tpool.total_count - tpool.num_allocated < count)
    {
        thread_pool_resize();
    }

    pthread_t *ret_threads = &tpool.threads[tpool.num_allocated];
    tpool.num_allocated += count;

    pthread_mutex_unlock(&tpool.mu);
    return ret_threads;
}

/* SIGNAL HANDLER */
void sigint_handler() // this allows program to finish cleanly on CTRL-C press
{
    printf("Handling SIGINT by ending coordination...\n");

    pthread_mutex_lock(&this_node.mu);
    this_node.end_coordination = 1;
    pthread_mutex_unlock(&this_node.mu);

    pthread_mutex_lock(&election_status.mu);
    pthread_cond_broadcast(&election_status.cond);
    pthread_mutex_unlock(&election_status.mu);
}

/* UTILS */
double get_elapsed_time_ms(struct timeval start)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return (now.tv_sec - start.tv_sec) * 1000.0 + (now.tv_usec - start.tv_usec) / 1000.0;
}

int free_peer_info()
{
    pthread_mutex_lock(&this_node.mu);
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        freeaddrinfo(this_node.peers[i].address_info);
    }
    pthread_mutex_unlock(&this_node.mu);
    return 0;
}

short get_my_link_info() // get connected nodes information in encoded form
{
    short link_info = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id)
            link_info = (link_info << 1) + 1; // link info includes self as connected
        else if (this_node.peers[i].connected)
            link_info = (link_info << 1) + 1;
        else
            link_info = link_info << 1;
    }
    return link_info;
}

// encode message to follow network protocol
long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info)
{
    return (type << 24) | (node_id << 16) | (term << 8) | path_or_link_info;
}

short get_msg_type(long msg)
{
    return (msg >> 24) & 0xFF;
}

short get_msg_node_id(long msg)
{
    return (msg >> 16) & 0xFF;
}

short get_msg_term(long msg)
{
    return (msg >> 8) & 0xFF;
}

short get_msg_path_info(long msg)
{
    return msg & 0xFF;
}

short get_msg_link_info(long msg)
{
    return msg & 0xFF;
}

int get_msg_connected_count(long msg)
{
    unsigned short link_info = get_msg_link_info(msg);
    int connected_count;
    for (connected_count = 0; link_info != 0; link_info = link_info >> 1)
    {
        if ((link_info & 0b1) == 1)
            connected_count += 1;
    }
    return connected_count - 1; // subtract one to exclude self
}

/* DATA HANDLERS */
int handle_data(long msg) // finds which handler function to call and spins-off thread calling that function
{
    void *handler;
    int handler_thr_err;

    int type = get_msg_type(msg);

    switch (type)
    {
    case heartbeat_msg:
        handler = handle_heartbeat;
        break;
    case election_msg:
        handler = handle_election_msg;
        break;
    case election_reply_msg:
        handler = handle_election_reply;
        break;
    case leader_msg:
        handler = handle_leader_msg;
        break;
    }

    if ((handler_thr_err = thread_pool_assign_task(handler, (void *)msg)))
    {
        fprintf(stderr, "Error with creating handler thread\n");
        return handler_thr_err;
    }

    return 0;
}

void *handle_heartbeat(void *void_data)
{
    long msg = (long)void_data;

    int sender_id = get_msg_node_id(msg);

    // reset heartbeat timeout
    pthread_mutex_lock(&this_node.mu);
    gettimeofday(&this_node.peers[sender_id].timeout_start, NULL);
    pthread_mutex_unlock(&this_node.mu);

    pthread_exit(NULL);
}

void *handle_election_msg(void *void_data)
{
    long msg = (long)void_data;

    int term = get_msg_term(msg);
    int node_id = get_msg_node_id(msg);
    int connected_count = get_msg_connected_count(msg);

    printf("Handling election msg received from node %d\n term = %d, connected_count = %d, link_info = %d\n", node_id, term, connected_count, get_msg_link_info(msg));

    pthread_mutex_lock(&this_node.mu);

    if (term == this_node.term)
    {
        if (connected_count > this_node.connected_count || (connected_count == this_node.connected_count && node_id > this_node.id)) // give vote
        {
            printf("Giving vote to node %d, for term %d\n", node_id, this_node.term);
            printf("My id = %d, term = %d, connected_count = %d\n", this_node.id, this_node.term, this_node.connected_count);

            struct send_args *reply_args = (struct send_args *)malloc(sizeof(struct send_args));

            reply_args->term = this_node.term;
            reply_args->peer = this_node.peers[node_id];
            thread_pool_assign_task(send_election_reply_msg, reply_args);
        }
        // else don't give vote (ignore msg)
        pthread_mutex_unlock(&this_node.mu);
    }
    else if (term > this_node.term) // we are in old term, so update term and start our own election
    {
        printf("election_msg from node %d received with higher term than current term. Updating term and starting leader election...\n", node_id);

        // atomically change term and votes received
        this_node.term = term;
        this_node.votes_received = 0;

        pthread_mutex_unlock(&this_node.mu);

        // broadcast election starting
        pthread_mutex_lock(&election_status.mu);
        election_status.status = starting;
        pthread_cond_broadcast(&election_status.cond);
        pthread_mutex_unlock(&election_status.mu);
    }
    // else received msg term is old, can ignore the msg

    pthread_exit(NULL);
}

void *handle_election_reply(void *void_data)
{
    long msg = (long)void_data;
    int term = get_msg_term(msg);
    int node_id = get_msg_node_id(msg);

    pthread_mutex_lock(&this_node.mu);

    // throw away old replies
    if (term != this_node.term)
    {
        pthread_mutex_unlock(&this_node.mu);
        pthread_exit(NULL);
    }

    // update link info of peer
    this_node.peers[node_id].link_info = get_msg_link_info(msg);

    // make sure not to count multiple votes from same peer
    for (int i = 0; i < this_node.votes_received; i++)
    {
        if (node_id == this_node.voted_peers[i]) // already received this vote, ignore
        {
            pthread_mutex_unlock(&this_node.mu);
            pthread_exit(NULL);
        }
    }

    // count vote
    printf("Received vote from node %d for term %d\n", node_id, term);
    printf("Now, votes_received = %d, connected_count = %d\n", this_node.votes_received + 1, this_node.connected_count);

    this_node.voted_peers[this_node.votes_received] = node_id; // keep track of whose vote
    ++this_node.votes_received;

    pthread_mutex_lock(&election_status.mu);
    pthread_cond_broadcast(&election_status.cond); // wake up check_election_result()
    pthread_mutex_unlock(&election_status.mu);

    pthread_mutex_unlock(&this_node.mu);
    pthread_exit(NULL);
}

void *handle_leader_msg(void *void_data)
{
    printf("Received leader message...\n");

    long msg = (long)void_data;

    // ignore old messages
    pthread_mutex_lock(&this_node.mu);
    if (get_msg_term(msg) != this_node.term)
    {
        pthread_mutex_unlock(&this_node.mu);
        pthread_exit(NULL);
    }

    // else, acknowledge leader, announce election is over
    printf("Acknowledging node %d is leader of term %d\n", get_msg_node_id(msg), this_node.term);
    printf("New path = %d\n", get_msg_path_info(msg));

    // keep track of leader
    this_node.leader_id = get_msg_node_id(msg);
    pthread_mutex_unlock(&this_node.mu);

    pthread_mutex_lock(&election_status.mu);
    election_status.status = inactive; // election is over
    pthread_cond_broadcast(&election_status.cond);
    pthread_mutex_unlock(&election_status.mu);

    pthread_exit(NULL);
}

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct peer_info *peer)
{
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    int status;

    if ((status = getaddrinfo(address, port, &hints, &peer->address_info)))
    {
        fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
        return -1;
    }
    return 0;
}

int prepare_socket(struct peer_info *peer)
{
    struct addrinfo *address_info = peer->address_info;
    if ((peer->socket = socket(address_info->ai_family, address_info->ai_socktype, address_info->ai_protocol)) == -1)
    {
        fprintf(stderr, "Error creating socket\n");
        return -1;
    }
    return 0;
}

int send_once(long msg, struct peer_info target) // helper function for msg sending
{
    int bytes_sent;
    struct addrinfo *address_info = target.address_info;

    if ((bytes_sent = sendto(target.socket, &msg, sizeof(long), 0, address_info->ai_addr, address_info->ai_addrlen)) == -1)
    {
        fprintf(stderr, "Error with sending data\n");
        return -1;
    }
    return 0;
}

void *send_heartbeat(void *void_args) // helper function for heartbeats
{
    // get args: (long msg, struct peer_info target, int *condition, pthread_mutex_t *mu)
    struct send_args *args = void_args;

    pthread_mutex_lock(args->mutex);
    while (!*args->condition)
    {
        pthread_mutex_unlock(args->mutex);
        int bytes_sent;
        struct addrinfo *address_info = args->peer.address_info;

        if ((bytes_sent = sendto(args->peer.socket, &args->msg, sizeof(long), 0, address_info->ai_addr, address_info->ai_addrlen)) == -1)
        {
            fprintf(stderr, "Error with sending data\n");
            free(args);
            pthread_exit(NULL);
        }

        // sleep for a bit between heartbeats
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 500 * 1000 * 1000; // 500ms
        nanosleep(&ts, NULL);

        pthread_mutex_lock(args->mutex);
    }

    pthread_mutex_unlock(args->mutex);
    free(args);

    pthread_exit(NULL);
}

void *recv_until(void *void_args) // for listening for messages
{
    // get args: (struct peer_info listener, int *condition, pthread_mutex_t *mu)
    struct recv_args *args = void_args;

    // have recvfrom() timeout after 1 second so it doesn't block forever
    struct timeval recv_to;
    recv_to.tv_sec = 1;
    recv_to.tv_usec = 0;
    setsockopt(args->peer.socket, SOL_SOCKET, SO_RCVTIMEO, &recv_to, sizeof(recv_to));

    // bind to port
    struct addrinfo *address_info = args->peer.address_info;
    if (bind(args->peer.socket, address_info->ai_addr, address_info->ai_addrlen) == -1)
    {
        fprintf(stderr, "Error with binding receiver to port\n");
        pthread_exit(NULL);
    }

    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));

    int recv_buf_size = 64; // big enough for our network protocols messages
    long recv_buf;

    pthread_mutex_lock(args->mutex);

    while (!*args->condition)
    {
        pthread_mutex_unlock(args->mutex);
        int bytes_received;
        if ((bytes_received = recvfrom(args->peer.socket, &recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen)) > 0)
        {
            handle_data(recv_buf);
        }
        pthread_mutex_lock(args->mutex);
    }

    pthread_mutex_unlock(args->mutex);
    free(args);

    pthread_exit(NULL);
}

int broadcast_heartbeat()
{
    pthread_mutex_lock(&this_node.mu);

    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id) // don't send message to oneself
            continue;

        struct send_args *args = (struct send_args *)malloc(sizeof(struct send_args));
        args->msg = encode_msg(heartbeat_msg, this_node.id, 0, 0);
        args->peer = this_node.peers[i];
        args->condition = &this_node.end_coordination;
        args->mutex = &this_node.mu;

        thread_pool_assign_task(send_heartbeat, args);
    }

    pthread_mutex_unlock(&this_node.mu);

    return 0;
}

void *send_election_reply_msg(void *void_args)
{
    // args: (int term, struct peer_info target)
    struct send_args *args = (struct send_args *)void_args;

    // always acquire locks in this order to avoid deadlocks
    pthread_mutex_lock(&this_node.mu);
    pthread_mutex_lock(&election_status.mu);

    // send election reply until election ends or term changes
    while (args->term == this_node.term && election_status.status == in_progress)
    {
        pthread_mutex_unlock(&election_status.mu);

        // send
        long msg = encode_msg(election_reply_msg, this_node.id, args->term, get_my_link_info());
        send_once(msg, args->peer);

        // sleep
        pthread_mutex_unlock(&this_node.mu);
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 500 * 1000 * 1000; // 500ms TODO: adjustable
        nanosleep(&ts, NULL);

        pthread_mutex_lock(&this_node.mu);
        pthread_mutex_lock(&election_status.mu);
    }

    pthread_mutex_unlock(&election_status.mu);
    pthread_mutex_unlock(&this_node.mu);

    free(args);

    pthread_exit(NULL);
}

void *broadcast_election_msg(void *void_args)
{
    // args: (int term)
    struct send_args *args = (struct send_args *)void_args;

    pthread_mutex_lock(&this_node.mu);
    pthread_mutex_lock(&election_status.mu);

    // send election reply until election ends or term changes
    while (args->term == this_node.term && election_status.status == in_progress && !this_node.end_coordination)
    {
        pthread_mutex_unlock(&election_status.mu);

        for (int i = 0; i < this_node.num_nodes; i++)
        {
            if (i == this_node.id)
                continue;

            // send
            long msg = encode_msg(election_msg, this_node.id, args->term, get_my_link_info());
            struct peer_info target = this_node.peers[i];
            send_once(msg, target);
        }

        // sleep
        pthread_mutex_unlock(&this_node.mu);
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 500 * 1000 * 1000; // 500ms TODO: adjustable
        nanosleep(&ts, NULL);

        pthread_mutex_lock(&this_node.mu);
        pthread_mutex_lock(&election_status.mu);
    }

    pthread_mutex_unlock(&election_status.mu);
    pthread_mutex_unlock(&this_node.mu);

    pthread_exit(NULL);
}

void *broadcast_leader_msg(void *void_args)
{
    // args: (int term, int path_info)
    struct send_args *args = (struct send_args *)void_args;

    pthread_mutex_lock(&this_node.mu);

    // send leader message until term changes
    while (args->term == this_node.term && !this_node.end_coordination)
    {
        for (int i = 0; i < this_node.num_nodes; i++)
        {
            if (i == this_node.id) // skip self
                continue;

            // send
            long msg = encode_msg(leader_msg, this_node.id, args->term, args->path_info);
            struct peer_info target = this_node.peers[i];
            send_once(msg, target);
        }

        // sleep
        pthread_mutex_unlock(&this_node.mu);
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 500 * 1000 * 1000; // 500ms TODO: adjustable
        nanosleep(&ts, NULL);

        pthread_mutex_lock(&this_node.mu);
    }
    pthread_mutex_unlock(&this_node.mu);
    pthread_exit(NULL);
}

/* COORDINATION FUNCTIONS */
int coordination()
{
    // start thread checking to start leader election
    thread_pool_assign_task(trigger_election, NULL);

    // start thread checking status of leader election
    thread_pool_assign_task(check_election_result, NULL);

    // being heartbeat timers and spinoff thread tracking heartbeat timers
    begin_heartbeat_timers();

    // for each other node, spinoff thread sending periodic heartbeats
    begin_heartbeats();

    // start thread listening for communication from other nodes
    begin_listening();

    return 0;
}

int begin_heartbeat_timers()
{
    pthread_mutex_lock(&this_node.mu);

    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == this_node.id)
            continue;
        gettimeofday(&this_node.peers[i].timeout_start, NULL); // set timeout start point
    }

    pthread_mutex_unlock(&this_node.mu);

    thread_pool_assign_task(track_heartbeat_timers, NULL); // start tracking heartbeat timeout

    return 0;
}

int begin_heartbeats()
{
    return broadcast_heartbeat();
}

int begin_listening() // listen for messages until coordination ends
{
    struct recv_args *args = (struct recv_args *)malloc(sizeof(struct recv_args));

    pthread_mutex_lock(&this_node.mu);
    args->peer = this_node.peers[this_node.id];
    args->condition = &this_node.end_coordination;
    args->mutex = &this_node.mu;
    pthread_mutex_unlock(&this_node.mu);

    thread_pool_assign_task(recv_until, args);

    return 0;
}

void *trigger_election() // TODO: add raft-style leader election option?
{
    while (!this_node.end_coordination)
    {
        pthread_mutex_lock(&this_node.mu);
        pthread_mutex_lock(&election_status.mu);

        while (election_status.status != starting && !this_node.end_coordination)
        {
            pthread_mutex_unlock(&this_node.mu);

            pthread_cond_wait(&election_status.cond, &election_status.mu);

            // to avoid deadlock, reacquire locks in correct order (this_node.mu -> election_status.mu)
            pthread_mutex_unlock(&election_status.mu);
            pthread_mutex_lock(&this_node.mu);
            pthread_mutex_lock(&election_status.mu);
        }

        pthread_mutex_unlock(&election_status.mu);
        pthread_mutex_unlock(&this_node.mu);

        bully_election();
    }

    return 0;
}

void *track_heartbeat_timers()
{
    sleep(5); // TODO: change this to hold until exchange heartbeats with everyone, currently give 5 seconds for everyone to get up and running

    pthread_mutex_lock(&this_node.mu);

    // loop through peers, checking if time elapsed > heartbeat timeout length
    while (!this_node.end_coordination)
    {
        for (int i = 0; i < this_node.num_nodes; i++)
        {
            if (this_node.peers[i].id == this_node.id)
                continue;
            if (this_node.peers[i].connected && get_elapsed_time_ms(this_node.peers[i].timeout_start) > HB_TIMEOUT_LEN)
            {
                this_node.connected_count -= 1;
                this_node.peers[i].connected = 0;
                thread_pool_assign_task(heartbeat_timeout_handler, (void *)(long)i);
            }
        }

        // check every 100ms
        pthread_mutex_unlock(&this_node.mu);
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 100 * 1000 * 1000;
        nanosleep(&ts, NULL);

        pthread_mutex_lock(&this_node.mu);
    }

    pthread_mutex_unlock(&this_node.mu);

    return 0;
}

void *heartbeat_timeout_handler(void *void_args)
{
    // args: (int peer_id)
    int peer_id = (long)void_args;

    pthread_mutex_lock(&this_node.mu);
    pthread_mutex_lock(&election_status.mu);

    printf("No heartbeat received from node %d! Starting leader election...\n", this_node.peers[peer_id].id);
    printf("Connected count is now %d\n", this_node.connected_count);

    // atomically update term and votes_received
    this_node.term++; // TODO: add mod M for wrap around
    this_node.votes_received = 0;
    election_status.status = starting; // to trigger election start

    pthread_cond_broadcast(&election_status.cond);
    pthread_mutex_unlock(&election_status.mu);
    pthread_mutex_unlock(&this_node.mu);

    return 0;
}

int bully_election()
{
    // get term
    pthread_mutex_lock(&this_node.mu);
    int term = this_node.term;
    pthread_mutex_unlock(&this_node.mu);

    // set election to in-progress
    pthread_mutex_lock(&election_status.mu);
    election_status.status = in_progress;
    pthread_cond_broadcast(&election_status.cond);
    pthread_mutex_unlock(&election_status.mu);

    // broadcast election messages for the term
    printf("Starting broadcast of election msgs (term %d)\n", term);

    struct send_args *args = (struct send_args *)malloc(sizeof(struct send_args));
    args->term = term;

    thread_pool_assign_task(broadcast_election_msg, args);

    return 0;
}

void *check_election_result() // thread checking election results periodically
{
    pthread_mutex_lock(&this_node.mu);

    while (!this_node.end_coordination) // check election results until program terminations
    {
        pthread_mutex_lock(&election_status.mu);

        // while not in election, just sleep
        while (election_status.status != in_progress && !this_node.end_coordination)
        {
            pthread_mutex_unlock(&this_node.mu);

            // wait for election-related update
            pthread_cond_wait(&election_status.cond, &election_status.mu);

            // to avoid deadlock, reacquire locks in correct order (this_node.mu -> election_status.mu)
            pthread_mutex_unlock(&election_status.mu);
            pthread_mutex_lock(&this_node.mu);
            pthread_mutex_lock(&election_status.mu);
        }

        // while election is active, check if we became leader
        while (election_status.status == in_progress && !this_node.end_coordination)
        {
            if (this_node.votes_received >= this_node.connected_count) // this node is leader
            {
                printf("I won leader election of term %d!\n", this_node.term);

                this_node.leader_id = this_node.id;

                // send out leader message until coordination algorithm is terminated
                int term = this_node.term;
                pthread_mutex_unlock(&this_node.mu);

                // announce election over
                election_status.status = inactive;
                pthread_cond_broadcast(&election_status.cond);
                pthread_mutex_unlock(&election_status.mu);

                printf("Sending out leader message...\n");

                struct send_args *args = (struct send_args *)malloc(sizeof(struct send_args));
                args->term = term;
                args->path_info = get_best_path();

                if (args->path_info == 0)
                {
                    fprintf(stderr, "NO PATH FOUND!!! Exiting...\n");
                    exit(1);
                }

                // start broadcasting leader msg until term changes
                thread_pool_assign_task(broadcast_leader_msg, args);
            }
            else // this node is not leader (yet)
            {
                // wait for election-related update
                printf("Did not win election yet...sleeping again\n");

                pthread_mutex_unlock(&this_node.mu);
                pthread_cond_wait(&election_status.cond, &election_status.mu);

                printf("Checking election result...\n");

                // to avoid deadlock, reacquire locks in correct order (this_node.mu -> election_status.mu)
                pthread_mutex_unlock(&election_status.mu);
                pthread_mutex_lock(&this_node.mu);
                pthread_mutex_lock(&election_status.mu);
            }
        }

        pthread_mutex_unlock(&election_status.mu);
        pthread_mutex_unlock(&this_node.mu);
    }
    return 0;
}

short path_struct_to_short(struct path p) // helper function to encode path information
{
    pthread_mutex_lock(&this_node.mu);

    short res = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == p.node1 || i == p.node2)
            res = (res << 1) + 1;
        else
            res = res << 1;
    }

    pthread_mutex_unlock(&this_node.mu);

    return res;
}

short get_best_path() // use global paths[] (ordered by priority, hardcoded value)
{
    // just check paths in order of priority, return first valid one
    for (int i = 0; i < NUM_PATHS; i++)
    {
        if (path_is_valid(paths[i]))
            return path_struct_to_short(paths[i]);
    }

    fprintf(stderr, "NO PATHS AVAILABLE!!!\n");
    return 0;
}

int path_is_valid(struct path p) // path should be pair of node ids
{
    pthread_mutex_lock(&this_node.mu);

    printf("Checking validity of path (node_%d, node_%d)\n", p.node1, p.node2);

    // "Note that if the leader cannot recieve any information from a node,
    // then the leader acts as if it recieved all-False array"
    // this makes sure I'm not using out of date information
    if (!this_node.peers[p.node1].connected || !this_node.peers[p.node2].connected)
    {
        pthread_mutex_unlock(&this_node.mu);
        return 0;
    }

    // make sure both nodes believe they are connected to each other
    short link_info1 = this_node.peers[p.node1].link_info;

    int offset = (this_node.num_nodes - 1) - p.node2; // e.g. num_nodes = 3, node2 = 1, offset = 1

    pthread_mutex_unlock(&this_node.mu);
    return (link_info1 >> offset) && 0x01;
}

int main(int argc, char **argv)
{
    // Initialize thread_pool
    thread_pool_init(20); // TODO: adjust this value as needed

    // setup SIGINT handler
    struct sigaction sigact;
    int sigact_status;

    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = sigint_handler;

    if ((sigact_status = sigaction(SIGINT, &sigact, NULL)) != 0)
    {
        fprintf(stderr, "Error creating sigaction. Exiting...\n");
        exit(-1);
    }

    // argv should be [number_of_nodes, node_info_file, my_node_id]
    if (argc != 4)
    {
        fprintf(stderr, "Error: expected 3 command line arguments (number of nodes, node info file, my node id), found: %d\n", argc - 1);
        exit(1);
    }

    // get number of nodes from command line args
    int num_nodes = strtol(argv[1], NULL, 10);

    // get list of peer node's info from command line args
    /*
    file format should be:
    id address port
    id address port
    ...
    */

    // open info file
    FILE *node_info_file;
    if ((node_info_file = fopen(argv[2], "r")) == NULL)
    {
        fprintf(stderr, "Error: no such file or directory %s\n", argv[2]);
        exit(1);
    }

    // fill peer info
    struct peer_info peers[num_nodes];
    for (int i = 0; i < num_nodes; i++)
    {
        char address[16];
        char port[16];

        if ((fscanf(node_info_file, "%d %15s %15s", &peers[i].id, address, port)) != 3)
        {
            fprintf(stderr, "Error reading node info file\n");
            fclose(node_info_file);
            exit(1);
        }

        prepare_address_info(address, port, &peers[i]);
        prepare_socket(&peers[i]);

        peers[i].connected = 1;
        peers[i].link_info = 0;
    }

    fclose(node_info_file);

    // initialize this_node struct
    pthread_mutex_init(&this_node.mu, NULL);
    this_node.peers = peers;
    this_node.num_nodes = num_nodes;

    // get this process's node id from command line args
    int my_id = strtol(argv[3], NULL, 10);
    this_node.id = my_id;

    // set term = 0, connected_count = num_nodes - 1, no disconnected nodes, path accordingly
    this_node.term = 0;
    this_node.connected_count = num_nodes - 1;
    this_node.peers[this_node.id].link_info = 15; // 1111 in binary, or all connected

    printf("Starting with connected_count = %d\n", this_node.connected_count);

    // no leader to start
    this_node.leader_id = -1;

    // initialize vote structures
    this_node.votes_received = 0;
    this_node.voted_peers = (int *)malloc(sizeof(int) * (num_nodes - 1));
    for (int i = 0; i < num_nodes - 1; i++)
    {
        this_node.voted_peers[i] = -1;
    }

    // setup election_status structure to signal election-related updates
    election_status.status = inactive;
    pthread_cond_init(&election_status.cond, NULL);
    pthread_mutex_init(&election_status.mu, NULL);

    // begin coordination algorithm
    coordination();

    // clean up thread pool
    // this waits for all threads to finish
    thread_pool_destroy();

    // clean up other memory
    printf("Freeing peer_info and voted_peers...\n");
    free_peer_info();
    free(this_node.voted_peers);

    printf("Done. Exiting main()\n");

    exit(0);
}