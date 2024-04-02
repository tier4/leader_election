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

struct path
{
    int node1;
    int node2;
};
struct thread_pool
{
    pthread_t *threads;
    int total_count;
    int num_allocated;
    pthread_mutex_t mu;
};

struct peer_info
{
    int id;
    struct timeval timeout_start;
    struct addrinfo *address_info;
    int socket;
    int connected;
    unsigned short link_info;
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

struct send_args // not all fields may be used
{
    long msg;
    struct peer_info peer;
    int *condition;
    pthread_mutex_t *mutex;
    int term;
    int path_info;
};

struct recv_args
{
    struct peer_info peer;
    int *condition;
    pthread_mutex_t *mutex;
};

struct condition_variable
{
    int status;
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

enum election_statuses
{
    inactive,    // not started or finished
    starting,    // about to start
    in_progress, // in progress
};

/* THREAD POOL FUNCTIONS */
int thread_pool_init(int count);
int thread_pool_destroy();
int thread_pool_resize();
int thread_pool_assign_task(void *func, void *args);
pthread_t *get_thread();
pthread_t *get_threads(int count);

/* SIGNAL HANDLER */
void sigint_handler();

/* UTILS*/
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();
long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info);
short get_my_link_info();
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
void *send_until(void *void_args);
void *recv_until(void *void_args);
int broadcast_until(long msg, int *condition, pthread_mutex_t *mu);
int broadcast_heartbeat();
void *send_election_reply_msg(void *void_args);
void *broadcast_election_msg(void *void_args);
void *broadcast_leader_msg(void *void_args);

/* COORDINATION FUNCTIONS */
int coordination();
int begin_heartbeat_timers();
int begin_heartbeats();
int begin_listening();
void *trigger_election();
void *track_heartbeat_timers();
void *heartbeat_timeout_handler(void *void_args);
int bully_election();
void *check_election_result();
short path_struct_to_short(struct path p);
short get_best_path();
int path_is_valid(struct path p);
int connected(int node1, int node2);