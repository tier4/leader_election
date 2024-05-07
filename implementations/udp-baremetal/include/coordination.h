#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <stdint.h>

/* STRUCTS */
struct path
{
    uint8_t node1;
    uint8_t node2;
};

struct peer_info
{
    uint8_t id;
    struct timeval timeout_start;
    struct addrinfo *send_addrinfo;
    struct addrinfo *listen_addrinfo;
    int send_socket;
    int listen_socket;
    uint8_t connected;
    uint8_t link_info;
    int has_voted;
};

struct coordination_node
{
    uint8_t id;
    uint8_t num_nodes;
    struct peer_info *peers;
    uint8_t term;
    uint8_t leader_id;
    int period;
    int timeout_threshold;
};

enum msg_type
{
    heartbeat_msg,
    election_msg,
    election_reply_msg,
    leader_msg
};

/* UTILS*/
uint8_t get_my_connected_count();
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();
uint8_t get_my_link_info();
uint64_t encode_msg(uint8_t type, uint8_t node_id, uint8_t term, uint8_t path_or_link_info);
uint8_t get_msg_type(uint64_t msg);
uint8_t get_msg_node_id(uint64_t msg);
uint8_t get_msg_term(uint64_t msg);
uint8_t get_msg_path_info(uint64_t msg);
uint8_t get_msg_link_info(uint64_t msg);
uint8_t get_msg_connected_count(uint64_t msg);
int compare_term(uint8_t term, uint8_t base_term);

/* DATA HANDLERS */
int handle_data(uint64_t msg);
int handle_heartbeat(uint64_t msg);
int handle_election_msg(uint64_t msg);
int handle_election_reply(uint64_t msg);
int handle_leader_msg(uint64_t msg);

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct addrinfo **res);
int get_socket(struct addrinfo *address_info);
int send_once(uint64_t msg, struct addrinfo *addrinfo, int sock);
int broadcast_heartbeat();
int broadcast_election_msg(uint8_t term);
int broadcast_leader_msg(uint8_t term, uint8_t path_info);

/* COORDINATION FUNCTIONS */
int coordination();
int heartbeat_timeout_handler();
int begin_election();
uint8_t path_struct_to_uint8_t(struct path p);
uint8_t get_best_path();
int path_is_valid(struct path p);