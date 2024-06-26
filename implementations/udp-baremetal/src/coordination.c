
#include <sys/resource.h>

#include "coordination.h"

// This is a mask for term:
// term is incremented like 0, 1, ..., MASK, 0, 1, ..., MASK, 0, ...
#define MASK 15

// Hardcoded paths (ORDERED BY PRIORITY)
#define NUM_PATHS 4
// assume in node_id order, we have (Main ECU, Sub ECU, Main VCU, Sub VCU)
// then highest priority path is (Main ECU, Main VCU) or (0, 2) w/node_ids
struct path paths[NUM_PATHS] = {{0, 2}, {0, 3}, {1, 2}, {1, 3}};

/* GLOBAL DATA */
struct coordination_node this_node;

uint8_t get_my_connected_count() {
    uint8_t connected_count = 0;
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (this_node.peers[i].connected) {
            connected_count++;
        }
    }
    return connected_count - 1; // subtract one to exclude self
}

double get_elapsed_time_ms(struct timeval start)
{
    struct timeval now;
    gettimeofday(&now, NULL);
    return (now.tv_sec - start.tv_sec) * 1000.0 + (now.tv_usec - start.tv_usec) / 1000.0;
}

void free_peer_info()
{
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        freeaddrinfo(this_node.peers[i].send_addrinfo);
        freeaddrinfo(this_node.peers[i].listen_addrinfo);
    }
}

uint8_t get_my_link_info() // get connected nodes information in encoded form
{
    uint8_t link_info = 0;
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
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
uint64_t encode_msg(uint8_t type, uint8_t node_id, uint8_t term, uint8_t path_or_link_info)
{
    return (type << 24) | (node_id << 16) | (term << 8) | path_or_link_info;
}

uint8_t get_msg_type(uint64_t msg)
{
    return (msg >> 24) & 0xFF;
}

uint8_t get_msg_node_id(uint64_t msg)
{
    return (msg >> 16) & 0xFF;
}

uint8_t get_msg_term(uint64_t msg)
{
    return (msg >> 8) & 0xFF;
}

uint8_t get_msg_path_info(uint64_t msg)
{
    return msg & 0xFF;
}

uint8_t get_msg_link_info(uint64_t msg)
{
    return msg & 0xFF;
}

uint8_t get_msg_connected_count(uint64_t msg)
{
    uint8_t link_info = get_msg_link_info(msg);
    uint8_t connected_count = 0;
    for (; link_info != 0; link_info = link_info >> 1) {
        if ((link_info & 0b1) == 1)
            connected_count += 1;
    }
    return connected_count - 1; // subtract one to exclude self
}

int compare_term(uint8_t term, uint8_t base_term)
{
    if (term == base_term) {
        return 0; // terms are the same
    } else if (((term + MASK + 1 - base_term) & MASK) < MASK / 2) {
        return 1; // term is larger than base_term
    } else {
        return -1; // term is smaller than base_term
    }
}

void update_timestamp(uint8_t node_id)
{
    if (!this_node.peers[node_id].connected) {
        fprintf(stderr, "Error: rejoin\n");
        exit(1);
    }

    gettimeofday(&this_node.peers[node_id].timeout_start, NULL);
}

void handle_data(uint64_t msg)
{
    uint8_t type = get_msg_type(msg);
    switch (type) {
    case heartbeat_msg:
        handle_heartbeat(msg);
        break;
    case election_msg:
        handle_election_msg(msg);
        break;
    case reply_msg:
        handle_reply_msg(msg);
        break;
    case leader_msg:
        handle_leader_msg(msg);
        break;
    default:
        fprintf(stderr, "Error: unrecognized message type received: %hhd\n", type);
        exit(1);
    }
}

void handle_heartbeat(uint64_t msg)
{
    uint8_t node_id = get_msg_node_id(msg);
    update_timestamp(node_id);
}

void handle_election_msg(uint64_t msg)
{
    uint8_t term = get_msg_term(msg);
    uint8_t node_id = get_msg_node_id(msg);
    uint8_t connected_count = get_msg_connected_count(msg);

    update_timestamp(node_id);

    if (compare_term(term, this_node.term) == 1) { // we are in old term, so update term and start our own election
        // atomically change term and votes received
        this_node.term = term;
        for (uint8_t i = 0; i < this_node.num_nodes; i++) {
            this_node.peers[i].has_voted = 0;
            this_node.peers[i].phase = sending_election_msg;
        }
    }
    
    if (compare_term(term, this_node.term) == 0) {
        if (connected_count > get_my_connected_count() || (connected_count == get_my_connected_count() && node_id < this_node.id))
        {
            // give vote (reply OK message)
            this_node.peers[node_id].phase = sending_reply_msg;
        }
        // else don't give vote (ignore msg)
    }

    // else received msg term is old, can ignore the msg

    if (connected_count < this_node.num_nodes) {
        this_node.in_emergency = 1;
    }
}

void handle_reply_msg(uint64_t msg)
{
    uint8_t term = get_msg_term(msg);
    uint8_t node_id = get_msg_node_id(msg);

    update_timestamp(node_id);

    if (compare_term(term, this_node.term) == -1) {
        // throw away old replies
        return;
    } else if (compare_term(term, this_node.term) == 1) {
        // must not happen
        fprintf(stderr, "Receiving larger term. Exiting...\n");
        exit(1);
    }

    // update link info of peer
    this_node.peers[node_id].link_info = get_msg_link_info(msg);
    this_node.peers[node_id].has_voted = 1;

    // count votes
    uint8_t votes_count = 0;
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (this_node.peers[i].has_voted == 1) {
            votes_count++;
        }
    }

    // check if became leader
    if (votes_count == get_my_connected_count()) { // this node is leader
        this_node.leader_id = this_node.id;

        uint8_t path_info = get_best_path();
        if (path_info == 0) {
            fprintf(stderr, "NO PATH FOUND!!! Exiting...\n");
            exit(1);
        }

        for (uint8_t i = 0; i < this_node.num_nodes; i++) {
            this_node.peers[i].phase = sending_leader_msg;
        }
    }
}

void handle_leader_msg(uint64_t msg)
{
    uint8_t term = get_msg_term(msg);
    uint8_t node_id = get_msg_node_id(msg);
    uint8_t path_info = get_msg_path_info(msg);

    update_timestamp(node_id);

    if (compare_term(term, this_node.term) == -1) {
        // throw away old leader messages
        return;
    } else if (compare_term(term, this_node.term) == 1) {
        // must not happen
        fprintf(stderr, "Receiving larger term. Exiting...\n");
        exit(1);
    }

    if (path_info != this_node.path_info) {
        this_node.path_info = path_info;
        fprintf(stderr, "Receiving new path: %hhd\n", path_info);
    }

    this_node.leader_id = node_id;

    for (uint8_t i = 0; i < this_node.num_nodes; i++)
        this_node.peers[i].phase = sending_heartbeat;
}

void prepare_address_info(char *address, char *port, struct addrinfo **res)
{
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    int status;

    if ((status = getaddrinfo(address, port, &hints, res))) {
        fprintf(stderr, "Error with getting address info, status = %s\n", gai_strerror(status));
        exit(1);
    }
}

int get_socket(struct addrinfo *address_info)
{
    int sock;
    sock = socket(address_info->ai_family, address_info->ai_socktype, address_info->ai_protocol);

    if (sock == -1) {
        fprintf(stderr, "Error creating socket\n");
        exit(1);
    }

    return sock;
}

uint8_t path_struct_to_uint8_t(struct path p) // helper function to encode path information
{
    uint8_t res = 0;
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (i == p.node1 || i == p.node2)
            res = (res << 1) + 1;
        else
            res = res << 1;
    }

    return res;
}

uint8_t get_best_path() // use global paths[] (ordered by priority, hardcoded value)
{
    // just check paths in order of priority, return first valid one
    for (uint8_t i = 0; i < NUM_PATHS; i++) {
        if (path_is_valid(paths[i]))
            return path_struct_to_uint8_t(paths[i]);
    }

    fprintf(stderr, "NO PATHS AVAILABLE!!!\n");
    exit(1);
}

int path_is_valid(struct path p) // path should be pair of node ids
{
    // "Note that if the leader cannot recieve any information from a node,
    // then the leader acts as if it recieved all-False array"
    // this makes sure I'm not using out of date information
    if (!this_node.peers[p.node1].connected || !this_node.peers[p.node2].connected) {
        return 0;
    }

    // make sure both nodes believe they are connected to each other
    uint8_t link_info1 = this_node.peers[p.node1].link_info;

    uint8_t offset = (this_node.num_nodes - 1) - p.node2; // e.g. num_nodes = 3, node2 = 1, offset = 1

    return (link_info1 >> offset) && 0x01;
}

void initialize_socket()
{
    struct timeval recv_to;
    recv_to.tv_sec = 0;
    recv_to.tv_usec = 1;

    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (i == this_node.id)
            continue;

        setsockopt(this_node.peers[i].listen_socket, SOL_SOCKET, SO_RCVTIMEO, &recv_to, sizeof(recv_to));

        // bind to port
        struct addrinfo *address_info = this_node.peers[i].listen_addrinfo;
        if (bind(this_node.peers[i].listen_socket, address_info->ai_addr, address_info->ai_addrlen) == -1) {
            fprintf(stderr, "Error with binding receiver to port\n");
            exit(1);
        }
    }

    if (this_node.id == 0) {
        setsockopt(this_node.autoware.listen_socket, SOL_SOCKET, SO_RCVTIMEO, &recv_to, sizeof(recv_to));

        // bind to port
        struct addrinfo *address_info = this_node.autoware.listen_addrinfo;
        if (bind(this_node.autoware.listen_socket, address_info->ai_addr, address_info->ai_addrlen) == -1) {
            fprintf(stderr, "Error with binding receiver to port\n");
            exit(1);
        }
    }
}

void send_once(uint64_t msg, struct addrinfo *addrinfo, int sock) // helper function for msg sending
{
    int bytes_sent;
    if ((bytes_sent = sendto(sock, &msg, sizeof(uint64_t), 0, addrinfo->ai_addr, addrinfo->ai_addrlen)) == -1) {
        fprintf(stderr, "Error with sending data\n");
        exit(1);
    }
}

void heartbeat_timeout_handler()
{
    this_node.term = (this_node.term + 1) & MASK;
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        this_node.peers[i].has_voted = 0;
        this_node.peers[i].phase = sending_election_msg;
    }
}

void check_heartbeat_timeout()
{
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (i == this_node.id || !this_node.peers[i].connected)
            continue;
        
        if (get_elapsed_time_ms(this_node.peers[i].timeout_start) > this_node.timeout_threshold) {
            this_node.peers[i].connected = 0;
            heartbeat_timeout_handler();
        }
    }
}

void check_messages()
{
    // receive data
    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));

    uint8_t recv_buf_size = 64; // big enough for our network protocols messages
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        if (i == this_node.id)
            continue;

        uint64_t recv_buf;
        while (recvfrom(this_node.peers[i].listen_socket, &recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen) > 0) {
            handle_data(recv_buf);
        }
    }
}

void check_autoware()
{
    // receive from autoware
    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    memset(&from, 0, sizeof(from));
    uint8_t recv_buf_size = 64;
    uint64_t recv_buf;
    if (recvfrom(this_node.autoware.listen_socket, &recv_buf, recv_buf_size, 0, (struct sockaddr *)&from, &fromlen) > 0) {
        this_node.end_coordination = 1;
        fprintf(stderr, "end coordination\n");
    }
}

void send_messages()
{
    for (uint8_t i = 0; i < this_node.num_nodes; i++)
    {
        if (i == this_node.id || !this_node.peers[i].connected)
            continue;

        uint64_t msg;

        switch (this_node.peers[i].phase)
        {
        case sending_heartbeat:
            msg = encode_msg(heartbeat_msg, this_node.id, 0, 0);
            break;
        case sending_election_msg:
            msg = encode_msg(election_msg, this_node.id, this_node.term, get_my_link_info());
            break;
        case sending_reply_msg:
            msg = encode_msg(reply_msg, this_node.id, this_node.term, get_my_link_info());
            break;
        case sending_leader_msg:
            uint8_t path_info = get_best_path();
            if (path_info != this_node.path_info) {
                this_node.path_info = path_info;
                fprintf(stderr, "Broadcasting new path: %hhd\n", path_info);
            }

            msg = encode_msg(leader_msg, this_node.id, this_node.term, path_info);
            
            if (this_node.id == 1 && this_node.in_emergency) {
                send_once(0, this_node.autoware.send_addrinfo, this_node.autoware.send_socket);
            }

            break;
        default:
            fprintf(stderr, "Error: unrecognized phase to node %hhd\n", i);
            exit(1);
        }

        send_once(msg, this_node.peers[i].send_addrinfo, this_node.peers[i].send_socket);
    }
}

void coordination()
{
    // initialize socket
    initialize_socket();

    while (this_node.end_coordination == 0) {
        struct timeval start_time;
        gettimeofday(&start_time, NULL);

        check_heartbeat_timeout();

        check_messages();

        if (this_node.id == 0) {
            check_autoware();
        }

        send_messages();

        // sleep until this_node.period[ms] passes
        while (1) {
            struct timeval now;
            gettimeofday(&now, NULL);
            int elapsed_time = (now.tv_sec - start_time.tv_sec) * 1000.0 + (now.tv_usec - start_time.tv_usec) / 1000.0;
            if (elapsed_time < this_node.period) {
                struct timespec ts;
                ts.tv_sec = 0;
                ts.tv_nsec = this_node.period * 1000 * 1000 / 10; // period/10[ms]
                nanosleep(&ts, NULL);
            } else {
                break;
            }
        }
    }
}

int main(int argc, char **argv)
{
    // set CPU priority
    setpriority(PRIO_PROCESS, 0, -20);

    // argv should be [number_of_nodes, node_info_file, my_node_id, period]
    if (argc != 3) {
        fprintf(stderr, "Error: expected 2 command line arguments (node info file, my node id), found: %d\n", argc - 1);
        exit(1);
    }

    // get this process's node id from command line args
    this_node.id = strtol(argv[2], NULL, 10);

    this_node.num_nodes = 4;
    this_node.period = 20; // ms
    this_node.timeout_threshold = 100; // ms

    // open info file
    FILE *node_info_file;
    if ((node_info_file = fopen(argv[1], "r")) == NULL) {
        fprintf(stderr, "Error: no such file or directory %s\n", argv[2]);
        exit(1);
    }

    // fill peer info
    struct peer_info peers[this_node.num_nodes];
    for (uint8_t i = 0; i < this_node.num_nodes; i++) {
        char send_addr[16];
        char listen_addr[16];
        char port[8][16];

        if ((fscanf(node_info_file, "%hhd %15s %15s %15s %15s %15s %15s %15s %15s %15s %15s",
                &peers[i].id, send_addr, listen_addr, port[0], port[1], port[2], port[3], port[4], port[5], port[6], port[7])) != 11) {
            fprintf(stderr, "Error reading node info file\n");
            fclose(node_info_file);
            exit(1);
        }

        prepare_address_info(send_addr, port[this_node.id * 2], &peers[i].send_addrinfo);
        prepare_address_info(listen_addr, port[this_node.id * 2 + 1], &peers[i].listen_addrinfo);
        peers[i].send_socket = get_socket(peers[i].send_addrinfo);
        peers[i].listen_socket = get_socket(peers[i].listen_addrinfo);

        peers[i].connected = 1;
        peers[i].link_info = 0;
        peers[i].has_voted = 0;

        if (this_node.id == 0)
            peers[i].phase = sending_leader_msg;
        else
            peers[i].phase = sending_heartbeat;
    }

    fclose(node_info_file);

    // for autoware
    if (this_node.id == 0) {
        char listen_addr[16] = "127.0.0.1";
        char port[16] = "8000";
        prepare_address_info(listen_addr, port, &this_node.autoware.listen_addrinfo);
        this_node.autoware.listen_socket = get_socket(this_node.autoware.listen_addrinfo);
    } else if (this_node.id == 1) {
        char send_addr[16] = "127.0.0.1";
        char port[16] = "8001";
        prepare_address_info(send_addr, port, &this_node.autoware.send_addrinfo);
        this_node.autoware.send_socket = get_socket(this_node.autoware.send_addrinfo);
    }

    // initialize this_node struct
    this_node.peers = peers;
    this_node.term = 0;
    this_node.peers[this_node.id].link_info = 15; // 1111 in binary, or all connected
    this_node.leader_id = 0;
    this_node.path_info = 10; // 1010 in binary, or Main ECU - Main VCU
    this_node.end_coordination = 0;
    this_node.in_emergency = 0;

    // begin coordination algorithm
    coordination();

    // clean up other memory
    free_peer_info();

    exit(0);
}
