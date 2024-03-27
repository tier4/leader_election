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

/* GLOBAL DATA */
struct coordination_node this_node;
int hb_timeout_len = 1000;

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

/* DATA HANDLERS */
int handle_data(char *data)
{
    // find which handler function to call and spinoff thread calling that function
    pthread_t handler_thread;
    int handler_thr_err;

    // TODO: expand this to handle other functions depending on data received
    if ((handler_thr_err = pthread_create(&handler_thread, NULL, handle_heartbeat, data)) != 0)
    {
        fprintf(stderr, "Errow with creating handler thread\n");
        return handler_thr_err;
    }
    return 0;
}

void *handle_heartbeat(void *void_data)
{
    char *data = (char *)void_data;
    int sender_id = strtol(data, NULL, 10);

    pthread_mutex_lock(&this_node.mu);
    gettimeofday(&this_node.peers[sender_id].timeout_start, NULL);
    pthread_mutex_unlock(&this_node.mu);

    printf("Received heartbeat from node %d\n", sender_id);

    free(data);
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

int send_until(struct peer_info *target, int *condition, pthread_mutex_t *mu)
{
    char msg[256]; // TODO: make this limit safe
    sprintf(msg, "%d", this_node.id);
    pthread_mutex_lock(mu);
    while (!*condition)
    {
        pthread_mutex_unlock(mu);
        int bytes_sent;
        struct addrinfo *address_info = target->address_info;
        if ((bytes_sent = sendto(target->socket, msg, strlen(msg), 0, address_info->ai_addr, address_info->ai_addrlen)) == -1)
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

    int recv_buf_size = 256; // TODO: make this safe
    char *recv_buf = (char *)malloc(recv_buf_size);
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

int broadcast_until(int *condition, pthread_mutex_t *mu)
{
    pthread_mutex_lock(&this_node.mu);
    pthread_t threads[this_node.num_nodes - 1];
    int thread_count = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id) // don't send message to oneself
            continue;
        struct udpinfo *send_args = (struct udpinfo *)malloc(sizeof(struct udpinfo));
        send_args->peer = &this_node.peers[i];
        send_args->condition = condition;
        send_args->mutex = mu;
        pthread_create(&threads[thread_count++], NULL, send_until_pthread, send_args);
    }
    pthread_mutex_unlock(&this_node.mu);
    return 0;
}

void *send_until_pthread(void *void_args)
{
    struct udpinfo *args = (struct udpinfo *)void_args;
    send_until(args->peer, args->condition, args->mutex);
    free(args);
    pthread_exit(NULL);
}

void *recv_until_pthread(void *void_args)
{
    struct udpinfo *args = (struct udpinfo *)void_args;
    recv_until(args->peer, args->condition, args->mutex);
    free(args);
    pthread_exit(NULL);
}

/* COORDINATION FUNCTIONS */
int begin_coordination()
{
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
        gettimeofday(&this_node.peers[i].timeout_start, NULL);
    }
    pthread_mutex_unlock(&this_node.mu);

    pthread_t hb_timer_thread;
    pthread_create(&hb_timer_thread, NULL, track_heartbeat_timers, NULL);
    return 0;
}

int begin_heartbeats()
{
    pthread_mutex_lock(&this_node.mu);
    int *condition = &this_node.end_coordination;
    pthread_mutex_t *mu = &this_node.mu;
    pthread_mutex_unlock(&this_node.mu);
    return broadcast_until(condition, mu);
}

int begin_listening()
{
    pthread_t listen_thread;

    struct udpinfo *recv_args = (struct udpinfo *)malloc(sizeof(struct udpinfo));

    pthread_mutex_lock(&this_node.mu);
    recv_args->peer = &this_node.peers[this_node.id];
    recv_args->condition = &this_node.end_coordination;
    recv_args->mutex = &this_node.mu;
    pthread_mutex_unlock(&this_node.mu);
    pthread_create(&listen_thread, NULL, recv_until_pthread, recv_args);

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
                printf("No heartbeat received from node %d!\n", this_node.peers[i].id);
            }
        }
        pthread_mutex_unlock(&this_node.mu);
        sleep(1); // check every 100ms, adjust this as needed
        pthread_mutex_lock(&this_node.mu);
    }
    pthread_mutex_unlock(&this_node.mu);
    return 0;
}

int main(int argc, char **argv)
{
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

    // begin coordination algorithm
    begin_coordination();

    sleep(60 * 5); // sleep for 5 minutes so I can test coordination

    pthread_mutex_lock(&this_node.mu);
    this_node.end_coordination = 1;
    pthread_mutex_unlock(&this_node.mu);

    free_peer_info();
    printf("Done. Exiting main()\n");

    sleep(1); // give threads time to finish cleanly

    exit(0);
}