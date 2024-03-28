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
    int connected;
};

struct coordination_node
{
    int id;
    int num_nodes;
    struct peer_info *peers;
    pthread_mutex_t mu;
    int end_coordination;
    int connected_count;
    int term;
    int leader_id;
    int votes_received;
    int *voted_peers;
};

struct send_args
{
    long *msg;
    struct peer_info *peer;
    int *condition;
    pthread_mutex_t *mutex;
};

struct recv_args
{
    struct peer_info *peer;
    int *condition;
    pthread_mutex_t *mutex;
};

struct leader_chosen_info
{
    int chosen;
    pthread_cond_t cond;
    pthread_mutex_t mu;
};

enum msg_type
{
    heartbeat_msg,
    election_msg,
    election_reply_msg,
    leader_msg
};

/* SIGNAL HANDLER */
void sigint_handler();

/* UTILS*/
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();
int join_and_free(pthread_t *threads, int count);
long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info);
short get_link_info();
short get_msg_type(long msg);
short get_msg_node_id(long msg);
short get_msg_term(long msg);
short get_msg_path_info(long msg);
short get_msg_link_info(long msg);
int get_msg_connected_count(long msg);

/* DATA HANDLERS */
int handle_data(long msg);
void *handle_heartbeat(void *void_data);
void *handle_election_msg(void *void_data);
void *handle_election_reply(void *void_data);
void *handle_leader_msg(void *void_data);

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct peer_info *peer);
int prepare_socket(struct peer_info *peer);
int send_until(long *msg, struct peer_info *target, int *condition, pthread_mutex_t *mu);
int recv_until(struct peer_info *listener, int *condition, pthread_mutex_t *mu);
pthread_t *broadcast_until(long *msg, int *condition, pthread_mutex_t *mu);
void *send_until_pthread(void *void_args);
void *recv_until_pthread(void *void_args);

/* COORDINATION FUNCTIONS */
int coordination();
pthread_t *begin_heartbeat_timers();
pthread_t *begin_heartbeats();
pthread_t *begin_listening();
int begin_leader_election();
void *track_heartbeat_timers();
int bully_election();