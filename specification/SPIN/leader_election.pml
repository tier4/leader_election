#define BUFFER_SIZE 20
#define NODE_NUM 6

// This is for representing multiarray for connected_count
typedef array {
    bool arr[NODE_NUM]
};

mtype = {Election, Reply, Leader}
chan network[NODE_NUM] = [BUFFER_SIZE] of {mtype, byte, byte, byte}
bool crash[NODE_NUM]
byte connected_count[NODE_NUM]
bool detected_timeout[NODE_NUM]
byte timeout_node[NODE_NUM]
array connected[NODE_NUM]
byte terms[NODE_NUM]
byte yes_count[NODE_NUM]
byte leader[NODE_NUM]
byte expected_leader

// termination on 4 nodes
// #define finished_election ( \
//     (crash[0] || (empty(network[0]) && !detected_timeout[0])) && \
//     (crash[1] || (empty(network[1]) && !detected_timeout[1])) && \
//     (crash[2] || (empty(network[2]) && !detected_timeout[2])) && \
//     (crash[3] || (empty(network[3]) && !detected_timeout[3])) \
// )

// termination on 4 nodes
#define finished_election ( \
    (crash[0] || (empty(network[0]) && !detected_timeout[0])) && \
    (crash[1] || (empty(network[1]) && !detected_timeout[1])) && \
    (crash[2] || (empty(network[2]) && !detected_timeout[2])) && \
    (crash[3] || (empty(network[3]) && !detected_timeout[3])) && \
    (crash[4] || (empty(network[4]) && !detected_timeout[4])) && \
    (crash[5] || (empty(network[5]) && !detected_timeout[5])) \
)

inline new_election(id) {
    yes_count[id] = 0;
    
    byte i;
    for (i : 0..(NODE_NUM-1)) {
        if
        :: connected[id].arr[i] ->
            network[i]!Election(id, terms[id], connected_count[id]);
        :: else ->
            ; // do nothing
        fi
    }
}

inline onTimeout(id, node_id) {
    detected_timeout[id] = false;
    connected_count[id]--;
    connected[id].arr[node_id] = false;
    terms[id]++;
    new_election(id);
}

inline onElection(id, node_id, term, count) {
    if
    :: term > terms[id] ->
        terms[id] = term;
        new_election(id);
    :: else ->
        ; // do nothing 
    fi

    if
    :: term == terms[id] ->
        if
        :: count > connected_count[id] ->
            network[node_id]!Reply(id, term, 0); // reply yes
        :: count == connected_count[id] ->
            if
            :: node_id < id ->
                network[node_id]!Reply(id, term, 0); // reply yes
            :: node_id == id ->
                assert(false);
            :: node_id > id ->
                ; // do nothing
            fi
        :: count < connected_count[id] ->
            ; // do nothing
        fi
    :: term < terms[id] ->
        ; // do nothing
    fi
}

inline onReply(id, node_id, term) {
    if
    :: term > terms[id] ->
        assert(false);
    :: term == terms[id] ->
        yes_count[id]++;
        if
        :: yes_count[id] == connected_count[id] -> // id can be a new leader!
            leader[id] = id;
            byte i;
            for (i : 0..(NODE_NUM-1)) {
                if
                :: i != id && connected[id].arr[i] ->
                    network[i]!Leader(id, term, 0);
                :: else ->
                    ; // do nothing
                fi
            }
        :: else ->
            ; // do nothing
        fi
    :: term < terms[id] ->
        ; // do nothing
    fi
}

inline onLeader(id, node_id, term) {
    if
    :: term > terms[id] ->
        assert(false);
    :: term == terms[id] ->
        leader[id] = node_id;
    :: term < terms[id] ->
        ; // do nothing
    fi
}

proctype node(byte id) {
    main_loop:

    // represent non-deterministic behaviors
    atomic {
        byte node_id, term, count;
        if
        :: detected_timeout[id] ->
            onTimeout(id, timeout_node[id]);
        :: network[id]?Election(node_id, term, count) ->
            onElection(id, node_id, term, count);
        :: network[id]?Reply(node_id, term, _) ->
            onReply(id, node_id, term);
        :: network[id]?Leader(node_id, term, _) ->
            onLeader(id, node_id, term);
        :: finished_election ->
            assert(leader[id] == expected_leader);
            goto end;
        fi
    }

    goto main_loop

    end:
}

init {
    // Initialize
    byte i, j;
    for (i : 0..(NODE_NUM-1)) {
        connected_count[i] = NODE_NUM - 1;
        detected_timeout[i] = false;
        for (j : 0..(NODE_NUM-1)) {
            if
            :: i == j ->
                connected[i].arr[j] = false;
            :: else ->
                connected[i].arr[j] = true;
            fi
        }
    }

    // invoke a node 0 crash in 4 nodes
    // crash[0] = true;
    // expected_leader = 1;
    // timeout_node[1] = 0;
    // timeout_node[2] = 0;
    // timeout_node[3] = 0;
    // detected_timeout[1] = true;
    // detected_timeout[2] = true;
    // detected_timeout[3] = true;

    // invoke a link 0-1 crash in 4 nodes
    // expected_leader = 2;
    // timeout_node[0] = 1;
    // timeout_node[1] = 0;
    // detected_timeout[0] = true;
    // detected_timeout[1] = true;

    // invoke a node 0 crash in 6 nodes
    crash[0] = true;
    expected_leader = 1;
    timeout_node[1] = 0;
    timeout_node[2] = 0;
    timeout_node[3] = 0;
    timeout_node[4] = 0;
    timeout_node[5] = 0;
    detected_timeout[1] = true;
    detected_timeout[2] = true;
    detected_timeout[3] = true;
    detected_timeout[4] = true;
    detected_timeout[5] = true;

    // start each process
    for (i : 0..(NODE_NUM-1)) {
        if
        :: !crash[i] ->
            run node(i);
        :: else
        fi
    }
}