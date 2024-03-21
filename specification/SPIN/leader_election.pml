#define BUFFER_SIZE 10
#define NODE_NUM 4

// This is for representing multiarray for connected_count
typedef array {
    bool arr[NODE_NUM]
};

mtype = {Timeout, Election, Reply, Leader}
chan network[NODE_NUM] = [BUFFER_SIZE] of {mtype, byte, byte, byte}
bool crash[NODE_NUM]
byte connected_count[NODE_NUM]
array connected[NODE_NUM]
byte terms[NODE_NUM]
byte yes_count[NODE_NUM]
byte leader[NODE_NUM]
byte expected_leader

#define finished_election ((crash[0] || empty(network[0])) && (crash[1] || empty(network[1])) && (crash[2] || empty(network[2])) && (crash[3] || empty(network[3])))

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
        :: network[id]?Timeout(node_id, _, _) ->
            onTimeout(id, node_id);
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
        for (j : 0..(NODE_NUM-1)) {
            if
            :: i == j ->
                connected[i].arr[j] = false;
            :: else ->
                connected[i].arr[j] = true;
            fi
        }
    }

    // invoke a crash
    if
    :: true ->
        // example 1: node 0 crash
        crash[0] = true;
        expected_leader = 1;
        network[1]!Timeout(0, 0, 0);
        network[2]!Timeout(0, 0, 0);
        network[3]!Timeout(0, 0, 0);
    // :: true ->
    //     // example 2: node 1 crash
    //     crash[1] = true;
    //     expected_leader = 0;
    //     network[0]!Timeout(1, 0, 0);
    //     network[2]!Timeout(1, 0, 0);
    //     network[3]!Timeout(1, 0, 0);
    // :: true ->
    //     // example 3: node 2 crash
    //     crash[2] = true;
    //     expected_leader = 0;
    //     network[0]!Timeout(2, 0, 0);
    //     network[1]!Timeout(2, 0, 0);
    //     network[3]!Timeout(2, 0, 0);
    // :: true ->
    //     // example 4: node 3 crash
    //     crash[3] = true;
    //     expected_leader = 0;
    //     network[0]!Timeout(3, 0, 0);
    //     network[1]!Timeout(3, 0, 0);
    //     network[2]!Timeout(3, 0, 0)
    // :: true ->
    //     // example 5: link 0-1 crash
    //     expected_leader = 2;
    //     network[0]!Timeout(1, 0, 0);
    //     network[1]!Timeout(0, 0, 0);
    // :: true ->
    //     // example 6: link 0-2 crash
    //     expected_leader = 1;
    //     network[0]!Timeout(2, 0, 0);
    //     network[2]!Timeout(0, 0, 0);
    // :: true ->
    //     // example 7: link 0-3 crash
    //     expected_leader = 1;
    //     network[0]!Timeout(3, 0, 0);
    //     network[3]!Timeout(0, 0, 0);
    // :: true ->
    //     // example 8: link 1-2 crash
    //     expected_leader = 0;
    //     network[1]!Timeout(2, 0, 0);
    //     network[2]!Timeout(1, 0, 0);
    // :: true ->
    //     // example 9: link 1-3 crash
    //     expected_leader = 0;
    //     network[1]!Timeout(3, 0, 0);
    //     network[3]!Timeout(1, 0, 0);
    // :: true ->
    //     // example 10: link 2-3 crash
    //     expected_leader = 0;
    //     network[2]!Timeout(3, 0, 0);
    //     network[3]!Timeout(2, 0, 0);
    // :: true ->
    //     // example 11: link 0-2 & link 0-3 crash
    //     expected_leader = 1;
    //     if
    //     :: network[0]!Timeout(2, 0, 0);
    //        network[0]!Timeout(3, 0, 0);
    //     :: network[0]!Timeout(3, 0, 0);
    //        network[0]!Timeout(2, 0, 0);
    //     fi
    //     network[2]!Timeout(0, 0, 0);
    //     network[3]!Timeout(0, 0, 0);
    // :: true ->
    //     // example 12: node 0 & node 2 crash
    //     crash[0] = true;
    //     crash[2] = true;
    //     expected_leader = 1;
    //     if
    //     :: network[1]!Timeout(0, 0, 0);
    //        network[1]!Timeout(2, 0, 0);
    //     :: network[1]!Timeout(2, 0, 0);
    //        network[1]!Timeout(0, 0, 0);
    //     fi
    //     if
    //     :: network[3]!Timeout(0, 0, 0);
    //        network[3]!Timeout(2, 0, 0);
    //     :: network[3]!Timeout(2, 0, 0);
    //        network[3]!Timeout(0, 0, 0);
    //     fi
    // :: true ->
    //     // example 13: node 1 & node 3 crash
    //     crash[1] = true;
    //     crash[3] = true;
    //     expected_leader = 0;
    //     if
    //     :: network[0]!Timeout(1, 0, 0);
    //        network[0]!Timeout(3, 0, 0);
    //     :: network[0]!Timeout(3, 0, 0);
    //        network[0]!Timeout(1, 0, 0);
    //     fi
    //     if
    //     :: network[2]!Timeout(1, 0, 0);
    //        network[2]!Timeout(3, 0, 0);
    //     :: network[2]!Timeout(3, 0, 0);
    //        network[2]!Timeout(1, 0, 0);
    //     fi
    fi

    // start each process
    for (i : 0..(NODE_NUM-1)) {
        if
        :: !crash[i] ->
            run node(i);
        :: else
        fi
    }
}