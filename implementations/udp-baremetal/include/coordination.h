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
    int node1;
    int node2;
};

struct peer_info
{
    uint16_t id;
    struct timeval timeout_start;
    struct addrinfo *send_addrinfo;
    struct addrinfo *listen_addrinfo;
    int send_socket;
    int listen_socket;
    int connected;
    uint16_t link_info;
    int election_status; // TODO: これに応じてheartbeatとして送るメッセージを決める
    int has_voted;
};

struct coordination_node
{
    uint16_t id;
    int num_nodes;
    struct peer_info *peers;
    uint16_t term;
    uint16_t leader_id;
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

enum election_status
{
    sending_heartbeat,
    sending_election_msg,
    sending_ok_msg,
    sending_leader_msg,
};

/* UTILS*/
int get_my_connected_count();
double get_elapsed_time_ms(struct timeval start);
int free_peer_info();
uint16_t get_my_link_info();
long encode_msg(uint16_t type, uint16_t node_id, uint16_t term, uint16_t path_or_link_info);
uint16_t get_msg_type(long msg);
uint16_t get_msg_node_id(long msg);
uint16_t get_msg_term(long msg);
uint16_t get_msg_path_info(long msg);
uint16_t get_msg_link_info(long msg);
int get_msg_connected_count(long msg);
int compare_term(uint16_t term, uint16_t base_term);

/* DATA HANDLERS */
int handle_data(long msg);
int handle_heartbeat(long msg);
int handle_election_msg(long msg);
int handle_election_reply(long msg);
int handle_leader_msg(long msg);

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct addrinfo **res);
int get_socket(struct addrinfo *address_info);
int send_once(long msg, struct addrinfo *addrinfo, int sock);
int broadcast_heartbeat();
int broadcast_election_msg(uint16_t term);
int broadcast_leader_msg(uint16_t term, short path_info);

/* COORDINATION FUNCTIONS */
int coordination();
int heartbeat_timeout_handler();
int begin_election();
short path_struct_to_short(struct path p);
short get_best_path();
int path_is_valid(struct path p);