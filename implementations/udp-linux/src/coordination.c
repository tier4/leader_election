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

struct peer_info
{
    int id;
    char *address;
    char *port;
    struct timeval timeout_start;
};

struct coordination_node
{
    int id;
    int num_nodes;
    struct peer_info *peers;
    pthread_mutex_t mu;
};

struct coordination_node this_node;
// set heartbeat timeout length (ms)
int hb_timeout_len = 1000;

struct udpinfo
{
    char *address;
    char *port;
    struct addrinfo *hints;
    int *condition;
    pthread_mutex_t *mutex;
};

double get_elapsed_time_ms(struct timeval start)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return (now.tv_sec - start.tv_sec) * 1000.0 + (now.tv_usec - start.tv_usec) / 1000.0;
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
    return 0;
}

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

int send_until(const char *address, const char *port, const struct addrinfo *hints, int *condition, pthread_mutex_t *mu)
{
    int status;
    struct addrinfo *serverinfo;

    if ((status = getaddrinfo(address, port, hints, &serverinfo)) != 0)
    {
        fprintf(stderr, "Error with getting address info (send), status = %s\n", gai_strerror(status));
        return -1;
    }

    int sockfd;
    if ((sockfd = socket(serverinfo->ai_family, serverinfo->ai_socktype, serverinfo->ai_protocol)) == -1)
    {
        fprintf(stderr, "Error with getting socket file descriptor (send)\n");
        freeaddrinfo(serverinfo);
        return -1;
    }

    char msg[256]; // TODO: make this limit safe
    // memset(msg, 0, 256);
    sprintf(msg, "%d", this_node.id);
    pthread_mutex_lock(mu);
    while (!*condition)
    {
        pthread_mutex_unlock(mu);
        int bytes_sent;
        if ((bytes_sent = sendto(sockfd, msg, strlen(msg), 0, serverinfo->ai_addr, serverinfo->ai_addrlen)) == -1)
        {
            fprintf(stderr, "Error with sending data\n");
            freeaddrinfo(serverinfo);
            return -1;
        }
        // printf("Sent data: %s\n", msg);
        sleep(1);
        pthread_mutex_lock(mu);
    }
    pthread_mutex_unlock(mu);
    freeaddrinfo(serverinfo);
    return 0;
}

int recv_until(const char *address, const char *port, const struct addrinfo *hints, int *condition, pthread_mutex_t *mu)
{
    int status;
    struct addrinfo *serverinfo;

    // fprintf(stderr, "calling getaddrinfo(%s, %s, hints, &serverinfo)\n", address, port);
    if ((status = getaddrinfo(address, port, hints, &serverinfo)) != 0)
    {
        fprintf(stderr, "Error with getting address info (receive), status = %s\n", gai_strerror(status));
        return status;
    }

    int sockfd;
    if ((sockfd = socket(serverinfo->ai_family, serverinfo->ai_socktype, serverinfo->ai_protocol)) == -1)
    {
        fprintf(stderr, "Error with getting socket file descriptor (receive)\n");
        freeaddrinfo(serverinfo);
        return -1;
    }

    if (bind(sockfd, serverinfo->ai_addr, serverinfo->ai_addrlen) == -1)
    {
        fprintf(stderr, "Error with binding receiver to port\n");
        freeaddrinfo(serverinfo);
        return -1;
    }

    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));

    int recv_buf_size = 500;
    char *recv_buf = (char *)malloc(recv_buf_size);
    pthread_mutex_lock(mu);
    while (!*condition)
    {
        pthread_mutex_unlock(mu);
        int bytes_received;
        if ((bytes_received = recvfrom(sockfd, recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen)) == -1)
        {
            fprintf(stderr, "Error with receiving data\n");
            freeaddrinfo(serverinfo);
            free(recv_buf);
            return -1;
        }
        // printf("Received data: %s\n", recv_buf);

        // copy data into new buffer so receive function can continue
        char *data_buf = (char *)malloc(recv_buf_size);
        strncpy(data_buf, recv_buf, recv_buf_size);

        // handle data (this function should quickly return)
        handle_data(data_buf);

        sleep(1);
        pthread_mutex_lock(mu);
    }
    pthread_mutex_unlock(mu);

    freeaddrinfo(serverinfo);
    free(recv_buf);
    return 0;
}

void *send_until_pthread(void *void_args)
{
    struct udpinfo *args = (struct udpinfo *)void_args;
    send_until(args->address, args->port, args->hints, args->condition, args->mutex);
    free(args);
    pthread_exit(NULL);
}

void *recv_until_pthread(void *void_args)
{
    struct udpinfo *args = (struct udpinfo *)void_args;
    recv_until(args->address, args->port, args->hints, args->condition, args->mutex);
    free(args);
    pthread_exit(NULL);
}

void *start_hb_timers()
{
    pthread_mutex_lock(&this_node.mu);
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == this_node.id)
            continue;
        gettimeofday(&this_node.peers[i].timeout_start, NULL);
    }
    while (1)
    {
        for (int i = 0; i < this_node.num_nodes; i++)
        {
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

int begin_coordination(int num_nodes, int my_id)
{
    // start heartbeat timeout timer
    pthread_t hb_timer_thread;
    pthread_create(&hb_timer_thread, NULL, start_hb_timers, NULL);

    // for each other node, spinoff thread sending periodic heartbeats
    int hb_con = 0;
    pthread_mutex_t hb_mu;
    pthread_mutex_init(&hb_mu, NULL);
    pthread_t hb_threads[num_nodes - 1];
    int hb_threads_count = 0;
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;

    pthread_mutex_lock(&this_node.mu);
    for (int i = 0; i < num_nodes; i++)
    {
        if (this_node.peers[i].id == my_id) // don't send message to oneself
            continue;
        struct udpinfo *send_args = (struct udpinfo *)malloc(sizeof(struct udpinfo));
        send_args->address = this_node.peers[i].address;
        send_args->port = this_node.peers[i].port;
        send_args->hints = &hints;
        send_args->condition = &hb_con;
        send_args->mutex = &hb_mu;
        pthread_create(&hb_threads[hb_threads_count++], NULL, send_until_pthread, send_args);
    }
    pthread_mutex_unlock(&this_node.mu);

    // start thread listening for communication from other nodes
    int recv_con = 0;
    pthread_t recv_thread;
    pthread_mutex_t recv_mu;
    pthread_mutex_init(&recv_mu, NULL);
    struct addrinfo recv_hints;
    memset(&recv_hints, 0, sizeof(recv_hints));
    recv_hints.ai_family = AF_INET;
    recv_hints.ai_socktype = SOCK_DGRAM;
    // recv_hints.ai_flags = AI_PASSIVE;

    // recv_until(nodes[my_id].address, nodes[my_id].port, &recv_hints, &recv_con, &recv_mu);

    struct udpinfo *recv_args = (struct udpinfo *)malloc(sizeof(struct udpinfo));

    pthread_mutex_lock(&this_node.mu);
    recv_args->address = this_node.peers[my_id].address;
    // fprintf(stderr, "this_node.peers[my_id].address = %s\n", this_node.peers[my_id].address);
    // recv_args->address = NULL;
    recv_args->port = this_node.peers[my_id].port;
    pthread_mutex_unlock(&this_node.mu);

    recv_args->hints = &recv_hints;
    recv_args->condition = &recv_con;
    recv_args->mutex = &recv_mu;
    pthread_create(&recv_thread, NULL, recv_until_pthread, recv_args);

    sleep(60 * 5); // sleep for 5 minutes so I can test heartbeats
    return 0;
}

int free_peer_info()
{
    pthread_mutex_lock(&this_node.mu);
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        free(this_node.peers[i].address);
        free(this_node.peers[i].port);
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
        peers[i].address = (char *)malloc(16); // assume IPv4 addresses (15 chars max)
        memset(peers[i].address, 0, 16);
        peers[i].port = (char *)malloc(16);
        memset(peers[i].port, 0, 16);
        if (fscanf(node_info_file, "%d %15s %15s", &peers[i].id, peers[i].address, peers[i].port) == EOF)
        {
            fprintf(stderr, "Error: unexpected end of file\n");
            fclose(node_info_file);
            exit(1);
        }
    }
    fclose(node_info_file);

    pthread_mutex_init(&this_node.mu, NULL);
    this_node.peers = peers;
    this_node.num_nodes = num_nodes;

    // get this process's node id from command line args
    int my_id = strtol(argv[3], NULL, 10);
    this_node.id = my_id;

    // begin coordination algorithm
    begin_coordination(num_nodes, my_id);

    free_peer_info();
    printf("Done. Exiting main()\n");

    exit(0);
}