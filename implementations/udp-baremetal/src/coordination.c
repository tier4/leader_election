#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include "coordination.h"
#include <signal.h>
#include <sys/resource.h>

// Hardcoded paths (ORDERED BY PRIORITY)
#define NUM_PATHS 4
// assume in node_id order, we have (Main ECU, Sub ECU, Main VCU, Sub VCU)
// then highest priority path is (Main ECU, Main VCU) or (0, 2) w/node_ids
struct path paths[NUM_PATHS] = {{0, 2}, {0, 3}, {1, 2}, {1, 3}};

/* GLOBAL DATA */
struct coordination_node this_node;

int period;
int timeout_threshold;

/* SIGNAL HANDLER */
void sigint_handler() // this allows program to finish cleanly on CTRL-C press
{
    printf("Handling SIGINT by ending coordination...\n");
    this_node.end_coordination = 1;
}

int get_my_connected_count() {
    int connected_count = 0;
    for (int i = 0; i < this_node.num_nodes; i++) {
        if (this_node.peers[i].connected) {
            connected_count++;
        }
    }
    return connected_count;
}

double get_elapsed_time_ms(struct timeval start)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return (now.tv_sec - start.tv_sec) * 1000.0 + (now.tv_usec - start.tv_usec) / 1000.0;
}

int free_peer_info()
{
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        freeaddrinfo(this_node.peers[i].send_addrinfo);
        freeaddrinfo(this_node.peers[i].listen_addrinfo);
    }
    return 0;
}

short get_my_link_info() // get connected nodes information in encoded form
{
    short link_info = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id)
            link_info = (link_info << 1) + 1; // link info includes self as connected
        else if (this_node.peers[i].connected)
            link_info = (link_info << 1) + 1;
        else
            link_info = link_info << 1;
    }
    return link_info;
}

// encode message to follow network protocol
long encode_msg(unsigned short type, unsigned short node_id, unsigned short term, unsigned short path_or_link_info)
{
    return (type << 24) | (node_id << 16) | (term << 8) | path_or_link_info;
}

short get_msg_type(long msg)
{
    return (msg >> 24) & 0xFF;
}

short get_msg_node_id(long msg)
{
    return (msg >> 16) & 0xFF;
}

short get_msg_term(long msg)
{
    return (msg >> 8) & 0xFF;
}

short get_msg_path_info(long msg)
{
    return msg & 0xFF;
}

short get_msg_link_info(long msg)
{
    return msg & 0xFF;
}

int get_msg_connected_count(long msg)
{
    unsigned short link_info = get_msg_link_info(msg);
    int connected_count;
    for (connected_count = 0; link_info != 0; link_info = link_info >> 1)
    {
        if ((link_info & 0b1) == 1)
            connected_count += 1;
    }
    return connected_count - 1; // subtract one to exclude self
}

/* DATA HANDLERS */
int handle_data(long msg)
{
    int type = get_msg_type(msg);
    switch (type)
    {
    case heartbeat_msg:
        return handle_heartbeat(msg);
    case election_msg:
        return handle_election_msg(msg);
    case election_reply_msg:
        return handle_election_reply(msg);
    case leader_msg:
        return handle_leader_msg(msg);
    }

    fprintf(stderr, "Error: unrecognized message type received\n");
    return -1;
}

int handle_heartbeat(long msg)
{
    int node_id = get_msg_node_id(msg);

    if (this_node.peers[node_id].heartbeat_exchanged && !this_node.peers[i].connected) {
        fprintf(stderr, "Error: rejoin\n");
        return -1;
    }

    this_node.peers[node_id].connected = 1;
    this_node.peers[node_id].heartbeat_exchanged = 1;
    gettimeofday(&this_node.peers[node_id].timeout_start, NULL);

    return 0;
}

int handle_election_msg(long msg)
{
    int term = get_msg_term(msg);
    int node_id = get_msg_node_id(msg);
    int connected_count = get_msg_connected_count(msg);

    if (term > this_node.term) // we are in old term, so update term and start our own election
    {
        // atomically change term and votes received
        this_node.term = term;
        this_node.votes_received = 0;
        begin_election();
    }
    
    if (term == this_node.term)
    {
        if (connected_count > get_my_connected_count() || (connected_count == get_my_connected_count() && node_id < this_node.id))
        {
            // give vote (reply OK message)
            long msg = encode_msg(election_reply_msg, this_node.id, term, get_my_link_info());
            send_once(msg, this_node.peers[node_id].send_addrinfo, this_node.peers[node_id].send_socket);
        }
        // else don't give vote (ignore msg)
    }

    // else received msg term is old, can ignore the msg

    return 0;
}

int handle_election_reply(long msg)
{
    int term = get_msg_term(msg);
    int node_id = get_msg_node_id(msg);

    if (term < this_node.term) {
        // throw away old replies
        return 0;
    } else if (term > this_node.term) {
        // is must not happen
        return -1;
    }

    // update link info of peer
    this_node.peers[node_id].link_info = get_msg_link_info(msg);

    // make sure not to count multiple votes from same peer
    for (int i = 0; i < this_node.votes_received; i++)
    {
        if (node_id == this_node.voted_peers[i]) // already received this vote, ignore
        {
            return 0;
        }
    }

    // count vote
    this_node.voted_peers[this_node.votes_received] = node_id; // keep track of whose vote
    ++this_node.votes_received;

    // check if became leader
    if (this_node.votes_received == get_my_connected_count()) // this node is leader
    {
        this_node.leader_id = this_node.id;

        short path_info = get_best_path();
        if (path_info == 0)
        {
            fprintf(stderr, "NO PATH FOUND!!! Exiting...\n");
            exit(1);
        }

        broadcast_leader_msg(term, path_info);
    }

    return 0;
}

int handle_leader_msg(long msg)
{
    int term = get_msg_term(msg);

    if (term < this_node.term) {
        // throw away old leader messages
        return 0;
    } else if (term > this_node.term) {
        // is must not happen
        return -1;
    }

    this_node.leader_id = get_msg_node_id(msg);

    return 0;
}

/* NETWORK FUNCTIONS */
int prepare_address_info(char *address, char *port, struct addrinfo **res)
{
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    int status;

    if ((status = getaddrinfo(address, port, &hints, res)))
    {
        fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
        return -1;
    }
    return 0;
}

int get_socket(struct addrinfo *address_info, int send_socket)
{
    int sock;
    if (send_socket)
        sock = socket(address_info->ai_family, address_info->ai_socktype | SOCK_NONBLOCK, address_info->ai_protocol);
    else
        sock = socket(address_info->ai_family, address_info->ai_socktype, address_info->ai_protocol);

    if (sock == -1)
    {
        fprintf(stderr, "Error creating socket\n");
        return -1;
    }

    return sock;
}

short path_struct_to_short(struct path p) // helper function to encode path information
{
    short res = 0;
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == p.node1 || i == p.node2)
            res = (res << 1) + 1;
        else
            res = res << 1;
    }

    return res;
}

short get_best_path() // use global paths[] (ordered by priority, hardcoded value)
{
    // just check paths in order of priority, return first valid one
    for (int i = 0; i < NUM_PATHS; i++)
    {
        if (path_is_valid(paths[i]))
            return path_struct_to_short(paths[i]);
    }

    fprintf(stderr, "NO PATHS AVAILABLE!!!\n");
    return 0;
}

int path_is_valid(struct path p) // path should be pair of node ids
{
    // "Note that if the leader cannot recieve any information from a node,
    // then the leader acts as if it recieved all-False array"
    // this makes sure I'm not using out of date information
    if (!this_node.peers[p.node1].connected || !this_node.peers[p.node2].connected)
    {
        return 0;
    }

    // make sure both nodes believe they are connected to each other
    short link_info1 = this_node.peers[p.node1].link_info;

    int offset = (this_node.num_nodes - 1) - p.node2; // e.g. num_nodes = 3, node2 = 1, offset = 1

    return (link_info1 >> offset) && 0x01;
}

int initialize_socket()
{
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (i == this_node.id)
            continue;

        // have recvfrom() timeout after 1 second so it doesn't block forever
        struct timeval recv_to;
        recv_to.tv_sec = 1;
        recv_to.tv_usec = 0;
        setsockopt(this_node.peers[i].listen_socket, SOL_SOCKET, SO_RCVTIMEO, &recv_to, sizeof(recv_to));

        // bind to port
        struct addrinfo *address_info = this_node.peers[i].listen_addrinfo;
        if (bind(this_node.peers[i].listen_socket, address_info->ai_addr, address_info->ai_addrlen) == -1)
        {
            fprintf(stderr, "Error with binding receiver to port\n");
            return -1;
        }
    }

    return 0;
}

int send_once(long msg, struct addrinfo *addrinfo, int sock) // helper function for msg sending
{
    int bytes_sent;
    if ((bytes_sent = sendto(sock, &msg, sizeof(long), 0, addrinfo->ai_addr, addrinfo->ai_addrlen)) == -1)
    {
        fprintf(stderr, "Error with sending data\n");
        return -1;
    }
    return 0;
}

int broadcast(long msg)
{
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id) // don't send message to oneself
            continue;

        send_once(msg, this_node.peers[i].send_addrinfo, this_node.peers[i].send_socket);
    }

    return 0;
}

int broadcast_heartbeat()
{
    long msg = encode_msg(heartbeat_msg, this_node.id, 0, 0);
    broadcast(msg);
    return 0;
}

int broadcast_election_msg(int term)
{
    long msg = encode_msg(election_msg, this_node.id, term, get_my_link_info());
    broadcast(msg);
    return 0;
}

int broadcast_leader_msg(int term, short path_info)
{
    long msg = encode_msg(leader_msg, this_node.id, term, path_info);
    broadcast(msg);
    return 0;
}

int begin_election()
{
    int term = this_node.term;
    broadcast_election_msg(term);
    return 0;
}

int heartbeat_timeout_handler()
{
    // atomically update term and votes_received
    this_node.term++; // TODO: add mod M for wrap around
    this_node.votes_received = 0;

    // start election
    begin_election();

    return 0;
}

int check_heartbeat_timeout()
{
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id)
            continue;
        
        if (this_node.peers[i].connected && get_elapsed_time_ms(this_node.peers[i].timeout_start) > timeout_threshold)
        {
            this_node.peers[i].connected = 0;
            heartbeat_timeout_handler();
        }
    }

    return 0;
}

int check_messages()
{
    // receive data
    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));

    int recv_buf_size = 64; // big enough for our network protocols messages
    for (int i = 0; i < this_node.num_nodes; i++)
    {
        if (this_node.peers[i].id == this_node.id)
            continue;

        long recv_buf;
        if (recvfrom(this_node.peers[i].listen_socket, &recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen) > 0)
        {
            if (handle_data(recv_buf) < 0) {
                return -1;
            }
        }
    }

    return 0;
}

/* COORDINATION FUNCTIONS */
int coordination()
{
    // initialize socket
    initialize_socket();

    while (1)
    {
        if (this_node.end_coordination)
            break;

        broadcast_heartbeat();

        check_heartbeat_timeout();

        if (check_messages() < 0)
            break;
    }

    return 0;
}

int main(int argc, char **argv)
{
    // set CPU priority
    setpriority(PRIO_PROCESS, 0, -20);

    // setup SIGINT handler
    struct sigaction sigact;
    int sigact_status;

    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_handler = sigint_handler;

    if ((sigact_status = sigaction(SIGINT, &sigact, NULL)) != 0)
    {
        fprintf(stderr, "Error creating sigaction. Exiting...\n");
        exit(-1);
    }

    // argv should be [number_of_nodes, node_info_file, my_node_id, period]
    if (argc != 6)
    {
        fprintf(stderr, "Error: expected 5 command line arguments (number of nodes, node info file, my node id, period, experiment id), found: %d\n", argc - 1);
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

    // get this process's node id from command line args
    int my_id = strtol(argv[3], NULL, 10);

    // get period for sending messages and checking timeout
    // heartbeat timeout threshold is 5 times larger than period
    period = strtol(argv[4], NULL, 10);
    timeout_threshold = 5 * period;

    // open info file
    FILE *node_info_file;
    if ((node_info_file = fopen(argv[2], "r")) == NULL)
    {
        fprintf(stderr, "Error: no such file or directory %s\n", argv[2]);
        exit(1);
    }

    // fill peer info
    struct peer_info peers[num_nodes];
    for (int i = 0; i < num_nodes; i++)
    {
        char send_addr[16];
        char listen_addr[16];
        char port[16];

        if ((fscanf(node_info_file, "%d %15s %15s %15s", &peers[i].id, send_addr, listen_addr, port)) != 4)
        {
            fprintf(stderr, "Error reading node info file\n");
            fclose(node_info_file);
            exit(1);
        }

        prepare_address_info(send_addr, port, &peers[i].send_addrinfo);
        prepare_address_info(listen_addr, port, &peers[i].listen_addrinfo);
        peers[i].send_socket = get_socket(peers[i].send_addrinfo, 1);
        peers[i].listen_socket = get_socket(peers[i].listen_addrinfo, 0);

        peers[i].connected = 1;
        peers[i].link_info = 0;
        peers[i].heartbeat_exchanged = 0;
    }

    fclose(node_info_file);

    // initialize this_node struct
    this_node.peers = peers;
    this_node.num_nodes = num_nodes;
    this_node.id = my_id;
    this_node.end_coordination = 0;

    // set term = 0, no disconnected nodes, path accordingly
    this_node.term = 0;
    this_node.peers[this_node.id].link_info = 15; // 1111 in binary, or all connected

    // no leader to start
    this_node.leader_id = -1;

    // initialize vote structures
    this_node.votes_received = 0;
    this_node.voted_peers = (int *)malloc(sizeof(int) * (num_nodes - 1));
    for (int i = 0; i < num_nodes - 1; i++)
    {
        this_node.voted_peers[i] = -1;
    }

    // begin coordination algorithm
    coordination();

    // clean up other memory
    free_peer_info();
    free(this_node.voted_peers);

    fclose(this_node.log);

    printf("Done. Exiting main()\n");

    exit(0);
}
