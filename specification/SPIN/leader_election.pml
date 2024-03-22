#define BUFFER_SIZE 10
#define NODE_NUM 4

// This is for representing multiarray for connected_count
typedef array {
    bool arr[NODE_NUM]
};
array connected[NODE_NUM]

// This is for representing multiarray for network
mtype = {Timeout, Election, Reply, Leader}
typedef multi_chan {
    chan interface[NODE_NUM] = [BUFFER_SIZE] of {mtype, byte, byte}
}
multi_chan network[NODE_NUM]

bool crash[NODE_NUM]
byte connected_count[NODE_NUM]
byte terms[NODE_NUM]
byte yes_count[NODE_NUM]
byte leader[NODE_NUM]
byte expected_leader

// termination on 4 nodes
#define finished_election ( \
    (crash[0] || (empty(network[0].interface[1]) && empty(network[0].interface[2]) && empty(network[0].interface[3]))) && \
    (crash[1] || (empty(network[1].interface[0]) && empty(network[1].interface[2]) && empty(network[1].interface[3]))) && \
    (crash[2] || (empty(network[2].interface[0]) && empty(network[2].interface[1]) && empty(network[2].interface[3]))) && \
    (crash[3] || (empty(network[3].interface[0]) && empty(network[3].interface[1]) && empty(network[3].interface[2]))) \
)

inline new_election(id) {
    yes_count[id] = 0;
    
    byte i;
    for (i : 0..(NODE_NUM-1)) {
        if
        :: connected[id].arr[i] ->
            network[i].interface[id]!Election(terms[id], connected_count[id]);
        :: else ->
            ; // do nothing
        fi
    }
}

inline onTimeout(id, node_id) {
    printf("timeout\n");
    connected_count[id]--;
    connected[id].arr[node_id] = false;
    terms[id]++;
    new_election(id);
}

inline onElection(id, node_id, term, count) {
    printf("election\n");
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
            network[node_id].interface[id]!Reply(term, 0); // reply yes
        :: count == connected_count[id] ->
            if
            :: node_id < id ->
                network[node_id].interface[id]!Reply(term, 0); // reply yes
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
                    network[i].interface[id]!Leader(term, 0);
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
        // timeout
        :: network[id].interface[0]?Timeout(_, _) ->
            onTimeout(id, 0);
        :: network[id].interface[1]?Timeout(_, _) ->
            onTimeout(id, 1);
        :: network[id].interface[2]?Timeout(_, _) ->
            onTimeout(id, 2);
        :: network[id].interface[3]?Timeout(_, _) ->
            onTimeout(id, 3);

        // election
        :: network[id].interface[0]?Election(term, count) ->
            onElection(id, 0, term, count);
        :: network[id].interface[1]?Election(term, count) ->
            onElection(id, 1, term, count);
        :: network[id].interface[2]?Election(term, count) ->
            onElection(id, 2, term, count);
        :: network[id].interface[3]?Election(term, count) ->
            onElection(id, 3, term, count);

        // reply
        :: network[id].interface[0]?Reply(term, _) ->
            onReply(id, 0, term);
        :: network[id].interface[1]?Reply(term, _) ->
            onReply(id, 1, term);
        :: network[id].interface[2]?Reply(term, _) ->
            onReply(id, 2, term);
        :: network[id].interface[3]?Reply(term, _) ->
            onReply(id, 3, term);

        // leader
        :: network[id].interface[0]?Leader(term, _) ->
            onLeader(id, 0, term);
        :: network[id].interface[1]?Leader(term, _) ->
            onLeader(id, 1, term);
        :: network[id].interface[2]?Leader(term, _) ->
            onLeader(id, 2, term);
        :: network[id].interface[3]?Leader(term, _) ->
            onLeader(id, 3, term);

        // termination
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
    // network[1].interface[0]!Timeout(0, 0);
    // network[2].interface[0]!Timeout(0, 0);
    // network[3].interface[0]!Timeout(0, 0);

    // invoke a link 0-1 crash in 4 nodes
    expected_leader = 2;
    network[1].interface[0]!Timeout(0, 0);
    network[0].interface[1]!Timeout(0, 0);

    // start each process
    for (i : 0..(NODE_NUM-1)) {
        if
        :: !crash[i] ->
            run node(i);
        :: else
        fi
    }
}

ltl p { <>(node@end) }