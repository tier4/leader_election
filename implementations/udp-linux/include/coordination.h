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
    struct addrinfo *send_addrinfo;
    struct addrinfo *listen_addrinfo;
    int send_socket;
    int listen_socket;
    int connected;
    unsigned short link_info;
    int heartbeat_exchanged; // check if initial heartbeat has been exchanged
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
    int election_status;

    FILE *log;
    int last_election_term_logged;
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
    in_progress, // in progress
};

enum log_type
{
    crash,
    election_end,
    rejoin_error,
};

/* THREAD POOL FUNCTIONS */
int thread_pool_init(int count);
int thread_pool_destroy();
int thread_pool_resize();
int thread_pool_assign_task(void *func, void *args);
pthread_t *get_thread();

/* SIGNAL HANDLER */
void sigint_handler();

/* UTILS*/
int write_to_log(int type);
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();
short get_my_link_info();
long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info);
short get_msg_type(long msg);
short get_msg_node_id(long msg);
short get_msg_term(long msg);
short get_msg_path_info(long msg);
short get_msg_link_info(long msg);
int get_msg_connected_count(long msg);

/* DATA HANDLERS */
int handle_data(long msg);
int handle_heartbeat(long msg);
int handle_election_msg(long msg);
int handle_election_reply(long msg);
int handle_leader_msg(long msg);

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct addrinfo **res);
int get_socket(struct addrinfo *address_info, int send_socket);
int send_once(long msg, struct addrinfo *addrinfo, int sock);
void *send_heartbeat(void *void_args);
void *recv_until(void *void_args);
int broadcast_heartbeat();
void *send_election_reply_msg(void *void_args);
void *broadcast_election_msg(void *void_args);
void *broadcast_leader_msg(void *void_args);

/* COORDINATION FUNCTIONS */
int coordination();
int begin_heartbeat_timers();
int begin_heartbeats();
int begin_listening();
void *track_heartbeat_timers();
void *heartbeat_timeout_handler(void *void_args);
int begin_election();
short path_struct_to_short(struct path p);
short get_best_path();
int path_is_valid(struct path p);