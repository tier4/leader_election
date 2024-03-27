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

/* GLOBAL DATA */
struct coordination_node this_node;
int hb_timeout_len = 1000;
pthread_cond_t leader_chosen = PTHREAD_COND_INITIALIZER;

/* SIGNAL HANDLER */
int sigint_handler()
{
    pthread_mutex_lock(&this_node.mu);
    this_node.end_coordination = 1;
    pthread_mutex_unlock(&this_node.mu);
    return 0;
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

int join_and_free(pthread_t *threads, int count)
{
    pthread_t *curr_thread = threads;
    for (int i = 0; i < count; i++)
    {
        pthread_join(curr_thread, NULL);
        curr_thread += 1;
    }
    free(threads);
    return 0;
}

long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info)
{
    return (type << 24) || (node_id << 16) || (term << 8) || path_or_link_info;
}

short get_msg_type(long msg)
{
    return (msg >> 24) && 0xFF;
}

short get_msg_node_id(long msg)
{
    return (msg >> 16) && 0xFF;
}

short get_msg_term(long msg)
{
    return (msg >> 8) && 0xFF;
}

short get_msg_path_info(long msg)
{
    return msg && 0xFF;
}

short get_msg_link_info(long msg)
{
    return msg && 0xFF;
}

/* DATA HANDLERS */
int handle_data(long msg)
{
    // find which handler function to call and spinoff thread calling that function
    pthread_t handler_thread;
    int handler_thr_err;

    int type = get_msg_type(msg);

    void *handler;

    switch (type)
    {
    case heartbeat_msg:
        handler = handle_heartbeat;
    case election_msg:
        handler = handle_election_msg;
    case election_reply_msg:
        handler = handle_election_reply;
    case leader_msg:
        handler = handle_leader_msg;
    }

    if ((handler_thr_err = pthread_create(&handler_thread, NULL, handler, (void *)msg)) != 0)
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

    printf("Received heartbeat from node %d\n", sender_id);

    pthread_exit(NULL);
}

void *handle_election_msg(void *void_data) // TODO:
{
    long msg = (long)void_data;

    pthread_exit(NULL);
}

void *handle_election_reply(void *void_data) // TODO:
{
    long msg = (long)void_data;

    // TODO: make sure not to count multiple votes from same peer

    // pthread_mutex_lock(&this_node.mu);
    // if (++this_node.votes_received == this_node.connected_count)
    // {
    //     this_node.is_leader = 1;
    //     pthread_cond_broadcast(&leader_chosen);
    // }
    // pthread_mutex_unlock(&this_node.mu);

    pthread_exit(NULL);
}

void *handle_leader_msg(void *void_data) // TODO:
{
    long msg = (long)void_data;

    // pthread_cond_broadcast(&leader_chosen);

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

int send_until(long *msg, struct peer_info *target, int *condition, pthread_mutex_t *mu)
{
    pthread_mutex_lock(mu);
    while (!*condition)
    {
        pthread_mutex_unlock(mu);
        int bytes_sent;
        struct addrinfo *address_info = target->address_info;
        if ((bytes_sent = sendto(target->socket, msg, sizeof(long), 0, address_info->ai_addr, address_info->ai_addrlen)) == -1)
        {
            fprintf(stderr, "Error with sending data\n");
            return -1;
        }
        // printf("Sent data: %s\n", msg);
        struct timespec ts;
        ts.tv_sec = 0;
        ts.tv_nsec = 250 * 1000 * 1000; // 250ms
        nanosleep(&ts, NULL);
        pthread_mutex_lock(mu);
    }
    pthread_mutex_unlock(mu);
    return 0;
}

int recv_until(struct peer_info *listener, int *condition, pthread_mutex_t *mu)
{
    struct addrinfo *address_info = listener->address_info;
    if (bind(listener->socket, address_info->ai_addr, address_info->ai_addrlen) == -1)
    {
        fprintf(stderr, "Error with binding receiver to port\n");
        return -1;
    }

    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));

    int recv_buf_size = 64;
    long *recv_buf = (long *)malloc(sizeof(long));
    pthread_mutex_lock(mu);
    while (!*condition)
    {
        pthread_mutex_unlock(mu);
        int bytes_received;
        if ((bytes_received = recvfrom(listener->socket, recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen)) == -1)
        {
            fprintf(stderr, "Error with receiving data\n");
            free(recv_buf);
            return -1;
        }
        // printf("Received data: %s\n", recv_buf);

        // copy data into new buffer so receive function can continue
        char *data_buf = (char *)malloc(recv_buf_size);
        strncpy(data_buf, recv_buf, recv_buf_size);

        // handle data (this function should quickly return)
        handle_data(data_buf);

        pthread_mutex_lock(mu);
    }
    pthread_mutex_unlock(mu);

    free(recv_buf);
    return 0;
}

pthread_t *broadcast_until(long *msg, int *condition, pthread_mutex_t *mu)
{
    pthread_mutex_lock(&this_node.mu);
    pthread_t *threads = (pthread_t *)malloc(sizeof(pthread_t) * (this_node.num_nodes - 1));
    int thread_count = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id) // don't send message to oneself
            continue;
        struct send_args *args = (struct send_args *)malloc(sizeof(struct send_args));
        args->msg = msg;
        args->peer = &this_node.peers[i];
        args->condition = condition;
        args->mutex = mu;
        pthread_create(&threads[thread_count++], NULL, send_until_pthread, args);
    }
    pthread_mutex_unlock(&this_node.mu);
    return threads;
}

void *send_until_pthread(void *void_args)
{
    struct send_args *args = (struct send_args *)void_args;
    send_until(args->msg, args->peer, args->condition, args->mutex);
    free(args->msg);
    free(args);
    pthread_exit(NULL);
}

void *recv_until_pthread(void *void_args)
{
    struct recv_args *args = (struct recv_args *)void_args;
    recv_until(args->peer, args->condition, args->mutex);
    free(args);
    pthread_exit(NULL);
}

/* COORDINATION FUNCTIONS */
int coordination()
{
    pthread_mutex_lock(&this_node.mu);
    int num_nodes = this_node.num_nodes;
    pthread_mutex_unlock(&this_node.mu);

    // being heartbeat timers and spinoff thread tracking heartbeat timers
    pthread_t *hb_timer_thread = begin_heartbeat_timers();

    // for each other node, spinoff thread sending periodic heartbeats
    pthread_t *hb_threads = begin_heartbeats();

    // start thread listening for communication from other nodes
    pthread_t *listening_thread = begin_listening();

    // wait for all threads to finish and then free allocated memory
    join_and_free(hb_timer_thread, 1);
    join_and_free(hb_threads, num_nodes - 1);
    join_and_free(listening_thread, 1);

    return 0;
}

pthread_t *begin_heartbeat_timers()
{
    pthread_mutex_lock(&this_node.mu);
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == this_node.id)
            continue;
        gettimeofday(&this_node.peers[i].timeout_start, NULL);
    }
    pthread_mutex_unlock(&this_node.mu);

    pthread_t *hb_timer_thread = (pthread_t *)malloc(sizeof(pthread_t));
    pthread_create(&hb_timer_thread, NULL, track_heartbeat_timers, NULL);
    return hb_timer_thread;
}

pthread_t *begin_heartbeats()
{
    pthread_mutex_lock(&this_node.mu);
    int *condition = &this_node.end_coordination;
    pthread_mutex_t *mu = &this_node.mu;
    long *msg = (long *)malloc(sizeof(long));
    *msg = encode_msg(heartbeat_msg, this_node.id, NULL, NULL);
    pthread_mutex_unlock(&this_node.mu);

    return broadcast_until(msg, condition, mu);
}

pthread_t *begin_listening()
{
    pthread_t *listen_thread = (pthread_t *)malloc(sizeof(pthread_t));

    struct recv_args *args = (struct recv_args *)malloc(sizeof(struct recv_args));

    pthread_mutex_lock(&this_node.mu);
    args->peer = &this_node.peers[this_node.id];
    args->condition = &this_node.end_coordination;
    args->mutex = &this_node.mu;
    pthread_mutex_unlock(&this_node.mu);
    pthread_create(&listen_thread, NULL, recv_until_pthread, args);

    return listen_thread;
}

int begin_leader_election() // TODO: add raft-style leader election option
{
    bully_election();
    return 0;
}

void *track_heartbeat_timers()
{
    pthread_mutex_lock(&this_node.mu);
    while (!this_node.end_coordination)
    {
        for (int i = 0; i < this_node.num_nodes; i++)
        {
            if (this_node.peers[i].id == this_node.id)
                continue;
            if (get_elapsed_time_ms(this_node.peers[i].timeout_start) > hb_timeout_len)
            {
                printf("No heartbeat received from node %d! Starting leader election...\n", this_node.peers[i].id);
                this_node.connected_count -= 1;
                // pthread_mutex_unlock(&this_node.mu); TODO: uncomment after testing heartbeat
                // begin_leader_election();
                // return;
            }
        }
        pthread_mutex_unlock(&this_node.mu);
        sleep(1); // check every 100ms, adjust this as needed
        pthread_mutex_lock(&this_node.mu);
    }
    pthread_mutex_unlock(&this_node.mu);
    return 0;
}

int bully_election()
{
    // pthread_mutex_t election_mu; // allocate in heap so doesn't disappear
    // pthread_mutex_init(&election_mu, NULL);
    // int election_over = 0;

    // pthread_mutex_lock(&this_node.mu);
    // int num_nodes = this_node.num_nodes;
    // this_node.term = this_node.term + 1; // TODO: add mod M for wrap around
    // long *msg = (long *)malloc(sizeof(long));
    // *msg = encode_msg(election_msg, this_node.id, this_node.term, NULL); // TODO: link information?
    // pthread_mutex_unlock(&this_node.mu);

    // int yes_count = 0;

    // pthread_t *threads = broadcast_until(msg, &election_over, &election_mu); // NOTE: this returns quickly!

    // wait(leader_chosen);

    // pthread_mutex_lock(&election_mu);
    // election_over = 1;
    // pthread_mutex_unlock(&election_mu);

    // join_and_free(threads, num_nodes - 1);

    return 0;
}

int main(int argc, char **argv)
{
    // setup SIGINT handler
    struct sigaction sigact;
    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = sigint_handler;

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
    FILE *node_info_file;
    if ((node_info_file = fopen(argv[2], "r")) == NULL)
    {
        fprintf(stderr, "Error: no such file or directory %s\n", argv[2]);
        exit(1);
    }
    struct peer_info peers[num_nodes];
    for (int i = 0; i < num_nodes; i++)
    {
        char *address = (char *)malloc(16);
        char *port = (char *)malloc(16);
        if (fscanf(node_info_file, "%d %15s %15s", &peers[i].id, address, port) == EOF)
        {
            fprintf(stderr, "Error: unexpected end of file\n");
            fclose(node_info_file);
            exit(1);
        }
        prepare_address_info(address, port, &peers[i]);
        prepare_socket(&peers[i]);
    }
    fclose(node_info_file);

    pthread_mutex_init(&this_node.mu, NULL);
    this_node.peers = peers;
    this_node.num_nodes = num_nodes;

    // get this process's node id from command line args
    int my_id = strtol(argv[3], NULL, 10);
    this_node.id = my_id;

    // set term = 0, connected_count = num_nodes - 1
    this_node.term = 0;
    this_node.connected_count = num_nodes - 1;

    // no leader to start
    this_node.is_leader = 0;

    // begin coordination algorithm
    coordination();

    // pthread_mutex_lock(&this_node.mu);
    // this_node.end_coordination = 1;
    // pthread_mutex_unlock(&this_node.mu);

    free_peer_info();

    printf("Done. Exiting main()\n");

    exit(0);
}