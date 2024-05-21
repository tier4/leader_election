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

enum msg_type
{
    heartbeat_msg,
    election_msg,
    reply_msg,
    leader_msg
};

enum election_phase
{
    sending_heartbeat,
    sending_election_msg,
    sending_reply_msg,
    sending_leader_msg
};

/* STRUCTS */
struct path
{
    uint8_t node1;
    uint8_t node2;
};

struct peer_info
{
    uint8_t id;
    uint8_t connected;
    uint8_t link_info;
    uint8_t has_voted;
    enum election_phase phase;
    int send_socket;
    int listen_socket;
    struct timeval timeout_start;
    struct addrinfo *send_addrinfo;
    struct addrinfo *listen_addrinfo;
};

struct coordination_node
{
    uint8_t id;
    uint8_t num_nodes;
    uint8_t term;
    uint8_t leader_id;
    uint8_t path_info;
    uint8_t end_coordination;
    uint8_t in_emergency;
    int period;
    int timeout_threshold;
    struct peer_info autoware;
    struct peer_info *peers;
};

uint8_t get_my_connected_count();
double get_elapsed_time_ms(struct timeval start);
void free_peer_info();
uint8_t get_my_link_info();
uint64_t encode_msg(uint8_t type, uint8_t node_id, uint8_t term, uint8_t path_or_link_info);
uint8_t get_msg_type(uint64_t msg);
uint8_t get_msg_node_id(uint64_t msg);
uint8_t get_msg_term(uint64_t msg);
uint8_t get_msg_path_info(uint64_t msg);
uint8_t get_msg_link_info(uint64_t msg);
uint8_t get_msg_connected_count(uint64_t msg);
int compare_term(uint8_t term, uint8_t base_term);
void update_timestamp(uint8_t node_id);
void handle_data(uint64_t msg);
void handle_heartbeat(uint64_t msg);
void handle_election_msg(uint64_t msg);
void handle_reply_msg(uint64_t msg);
void handle_leader_msg(uint64_t msg);
void prepare_address_info(char *address, char *port, struct addrinfo **res);
int get_socket(struct addrinfo *address_info);
void send_once(uint64_t msg, struct addrinfo *addrinfo, int sock);
void coordination();
void heartbeat_timeout_handler();
void begin_election();
uint8_t path_struct_to_uint8_t(struct path p);
uint8_t get_best_path();
int path_is_valid(struct path p);
