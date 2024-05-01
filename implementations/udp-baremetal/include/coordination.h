#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/time.h>

/* STRUCTS */
struct path
{
    int node1;
    int node2;
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
    int election_status; // TODO: これに応じてheartbeatとして送るメッセージを決める
    int has_voted;
};

struct coordination_node
{
    int id;
    int num_nodes;
    struct peer_info *peers;
    int term;
    int leader_id;
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
int get_socket(struct addrinfo *address_info);
int send_once(long msg, struct addrinfo *addrinfo, int sock);
int broadcast_heartbeat();
int broadcast_election_msg(int term);
int broadcast_leader_msg(int term, short path_info);

/* COORDINATION FUNCTIONS */
int coordination();
int heartbeat_timeout_handler();
int begin_election();
short path_struct_to_short(struct path p);
short get_best_path();
int path_is_valid(struct path p);