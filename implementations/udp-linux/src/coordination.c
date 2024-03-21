#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

struct udpinfo
{
    char *address;
    char *port;
    struct addrinfo *hints;
    int *condition;
    pthread_mutex_t *mutex;
};

int send_until(const char *address, const char *port, const struct addrinfo *hints, int *condition, pthread_mutex_t *mu)
{
    int status;
    struct addrinfo *serverinfo;

    if ((status = getaddrinfo(address, port, hints, &serverinfo)) != 0)
    {
        fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
        return -1;
    }

    int sockfd;
    if ((sockfd = socket(serverinfo->ai_family, serverinfo->ai_socktype, serverinfo->ai_protocol)) == -1)
    {
        fprintf(stderr, "Error with getting socket file descriptor\n");
        freeaddrinfo(serverinfo);
        return -1;
    }

    char *msg = "hello network programming";
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
        printf("Sent data: %s\n", msg);
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

    if ((status = getaddrinfo(address, port, hints, &serverinfo)) != 0)
    {
        fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
    }

    int sockfd;
    if ((sockfd = socket(serverinfo->ai_family, serverinfo->ai_socktype, serverinfo->ai_protocol)) == -1)
    {
        fprintf(stderr, "Error with getting socket file descriptor\n");
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
    int fromlen = sizeof(from);
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
        printf("Received data: %s\n", recv_buf);
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
}

void *recv_until_pthread(void *void_args)
{
    struct udpinfo *args = (struct udpinfo *)void_args;
    recv_until(args->address, args->port, args->hints, args->condition, args->mutex);
}

int main(int argc, char **argv)
{
    // spinoff thread to send until send_con == true
    int send_con = 0;

    struct addrinfo send_hints;
    memset(&send_hints, 0, sizeof(send_hints));
    send_hints.ai_family = AF_INET;
    send_hints.ai_socktype = SOCK_DGRAM;
    send_hints.ai_flags = AI_PASSIVE;

    // send in new thread
    pthread_t send_thread;
    struct udpinfo send_args;
    int snd_thr_err;
    pthread_mutex_t send_mu;

    // setup args
    memset(&send_args, 0, sizeof(send_args));
    send_args.address = NULL;
    send_args.port = "3054";
    send_args.hints = &send_hints;
    send_args.condition = &send_con;
    send_args.mutex = &send_mu;

    if ((snd_thr_err = pthread_create(&send_thread, NULL, send_until_pthread, &send_args)) != 0)
    {
        printf("Error with creating send thread, exiting...\n");
        exit(snd_thr_err);
    }
    // send_until(NULL, "3054", &send_hints, &send_con);

    // spinoff thread to receive until recv_con == true
    int recv_con = 0;

    struct addrinfo recv_hints;
    memset(&recv_hints, 0, sizeof(recv_hints));
    recv_hints.ai_family = AF_INET;
    recv_hints.ai_socktype = SOCK_DGRAM;
    recv_hints.ai_flags = AI_PASSIVE;

    // receive in new thread
    pthread_t recv_thread;
    struct udpinfo recv_args;
    int recv_thr_err;
    pthread_mutex_t recv_mu;

    memset(&recv_args, 0, sizeof(recv_args));
    recv_args.address = NULL;
    recv_args.port = "3054";
    recv_args.hints = &recv_hints;
    recv_args.condition = &recv_con;
    recv_args.mutex = &recv_mu;

    if ((recv_thr_err = pthread_create(&recv_thread, NULL, recv_until_pthread, &recv_args)) != 0)
    {
        printf("Error with creating receive thread, exiting...\n");
        exit(recv_thr_err);
    }
    // recv_until(NULL, "3054", &recv_hints, &recv_con);

    // sleep for a while and then set send_con and recv_con to true
    sleep(10);
    pthread_mutex_lock(&send_mu);
    send_con = 1;
    pthread_mutex_unlock(&send_mu);
    pthread_mutex_lock(&recv_mu);
    recv_con = 1;
    pthread_mutex_unlock(&recv_mu);
    pthread_join(send_thread, NULL);
    pthread_join(recv_thread, NULL);

    printf("Done. Exiting main()\n");

    exit(0);
}