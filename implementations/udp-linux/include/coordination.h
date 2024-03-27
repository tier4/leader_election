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

/* STRUCTS */
struct peer_info
{
    int id;
    struct timeval timeout_start;
    struct addrinfo *address_info;
    int socket;
};

struct coordination_node
{
    int id;
    int num_nodes;
    struct peer_info *peers;
    pthread_mutex_t mu;
    int end_coordination;
};

struct udpinfo
{
    struct peer_info *peer;
    int *condition;
    pthread_mutex_t *mutex;
};

/* UTILS*/
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();

/* DATA HANDLERS */
int handle_data(char *data);
void *handle_heartbeat(void *void_data);

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct peer_info *peer);
int prepare_socket(struct peer_info *peer);
int send_until(struct peer_info *target, int *condition, pthread_mutex_t *mu);
int recv_until(struct peer_info *listener, int *condition, pthread_mutex_t *mu);
int broadcast_until(int *condition, pthread_mutex_t *mu);
void *send_until_pthread(void *void_args);
void *recv_until_pthread(void *void_args);

/* COORDINATION FUNCTIONS */
int begin_coordination(int num_nodes, int my_id);
int begin_heartbeat_timers();
int begin_heartbeats();
int begin_listening();
void *track_heartbeat_timers();