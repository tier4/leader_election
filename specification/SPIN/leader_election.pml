#define BUFFER_SIZE 10
#define NODE_NUM 4

// This is for representing multiarray for connected_count
typedef array {
    byte arr[NODE_NUM]
};

mtype = {Timeout, Election, Reply, Leader}
chan network[NODE_NUM] = [BUFFER_SIZE] of {mtype, byte, byte, byte}
byte crash[NODE_NUM]
byte connected_count[NODE_NUM]
array connected[NODE_NUM]
byte election_ids[NODE_NUM]
byte yes_count[NODE_NUM]
byte leader[NODE_NUM]
byte expected_leader

#define finished_election (len(network[0]) == 0 && len(network[1]) == 0 && len(network[2]) == 0 && len(network[3]) == 0)

inline new_election(id) {
    yes_count[id] = 0;
    
    byte i;
    for (i : 0..3) {
        if
        :: connected[id].arr[i] ->
            network[i]!Election(id, election_ids[id], connected_count[id]);
        :: else ->
            ; // do nothing
        fi
    }
}

inline onTimeout(id, node_id) {
    connected_count[id] = connected_count[id] - 1;
    connected[id].arr[node_id] = 0;
    election_ids[id] = election_ids[id] + 1;
    new_election(id);
}

inline onElection(id, node_id, election_id, count) {
    if
    :: election_id > election_ids[id] ->
        election_ids[id] = election_id;
        new_election(id);
    :: election_id == election_ids[id] ->
        if
        :: count > connected_count[id] ->
            network[node_id]!Reply(id, election_id, 1);
        :: count == connected_count[id] ->
            if
            :: node_id < id ->
                network[node_id]!Reply(id, election_id, 1);
            :: node_id == id ->
                assert(false);
            :: node_id > id ->
                network[node_id]!Reply(id, election_id, 0);
            fi
        :: count < connected_count[id] ->
            network[node_id]!Reply(id, election_id, 0);
        fi
    :: election_id < election_ids[id] ->
        ; // do nothing
    fi
}

inline onReply(id, node_id, election_id, yes) {
    if
    :: election_id > election_ids[id] ->
        assert(false);
    :: election_id == election_ids[id] ->
        if
        :: yes == 1 ->
            yes_count[id] = yes_count[id] + 1;
            if
            :: yes_count[id] == connected_count[id] ->
                leader[id] = id;
                byte i;
                for (i : 0..3) {
                    if
                    :: i != id && connected[id].arr[i] ->
                        network[i]!Leader(id, election_id, 0);
                    :: else ->
                        ; // do nothing
                    fi
                }
            :: else ->
                ; // do nothing
            fi
        :: else ->
            ; // do nothing
        fi
    :: election_id < election_ids[id] ->
        ; // do nothing
    fi
}

inline onLeader(id, node_id, election_id) {
    if
    :: election_id > election_ids[id] ->
        assert(false);
    :: election_id == election_ids[id] ->
        leader[id] = node_id;
    :: election_id < election_ids[id] ->
        ; // do nothing
    fi
}

proctype node(byte id) {
    main_loop:

    atomic {
        byte node_id, election_id, count, yes;
        if
        :: crash[id] == 1 ->
            ;
        :: network[id]?Timeout(node_id, _, _) ->
            onTimeout(id, node_id);
        :: network[id]?Election(node_id, election_id, count) ->
            onElection(id, node_id, election_id, count);
        :: network[id]?Reply(node_id, election_id, yes) ->
            onReply(id, node_id, election_id, yes);
        :: network[id]?Leader(node_id, election_id, _) ->
            onLeader(id, node_id, election_id);
        :: finished_election ->
            ;
        fi
    }

    goto main_loop
}

init {
    byte i, j;
    for (i : 0..3) {
        connected_count[i] = 3;
        for (j : 0..3) {
            if
            :: i == j ->
                connected[i].arr[j] = 0;
            :: else ->
                connected[i].arr[j] = 1;
            fi
        }
    }

    if
    :: 1 == 1 ->
        // example 1: node 0 crash
        crash[0] = 1;
        expected_leader = 1;
        network[1]!Timeout(0, 0, 0);
        network[2]!Timeout(0, 0, 0);
        network[3]!Timeout(0, 0, 0);
    :: 1 == 1 ->
        // example 2: node 1 crash
        crash[1] = 1;
        expected_leader = 0;
        network[0]!Timeout(1, 0, 0);
        network[2]!Timeout(1, 0, 0);
        network[3]!Timeout(1, 0, 0);
    :: 1 == 1 ->
        // example 3: node 2 crash
        crash[2] = 1;
        expected_leader = 0;
        network[0]!Timeout(2, 0, 0);
        network[1]!Timeout(2, 0, 0);
        network[3]!Timeout(2, 0, 0);
    :: 1 == 1 ->
        // example 4: node 3 crash
        crash[3] = 1;
        expected_leader = 0;
        network[0]!Timeout(3, 0, 0);
        network[1]!Timeout(3, 0, 0);
        network[2]!Timeout(3, 0, 0)
    :: 1 == 1 ->
        // example 5: link 0-1 crash
        expected_leader = 2;
        network[0]!Timeout(1, 0, 0);
        network[1]!Timeout(0, 0, 0);
    :: 1 == 1 ->
        // example 6: link 0-2 crash
        expected_leader = 1;
        network[0]!Timeout(2, 0, 0);
        network[2]!Timeout(0, 0, 0);
    :: 1 == 1 ->
        // example 7: link 0-3 crash
        expected_leader = 1;
        network[0]!Timeout(3, 0, 0);
        network[3]!Timeout(0, 0, 0);
    :: 1 == 1 ->
        // example 8: link 1-2 crash
        expected_leader = 0;
        network[1]!Timeout(2, 0, 0);
        network[2]!Timeout(1, 0, 0);
    :: 1 == 1 ->
        // example 9: link 1-3 crash
        expected_leader = 0;
        network[1]!Timeout(3, 0, 0);
        network[3]!Timeout(1, 0, 0);
    :: 1 == 1 ->
        // example 10: link 2-3 crash
        expected_leader = 0;
        network[2]!Timeout(3, 0, 0);
        network[3]!Timeout(2, 0, 0);
    fi

    for (i : 0..3) {
        run node(i);
    }
}


#define elect_leader0 (crash[0] == 1 || leader[0] == expected_leader)
#define elect_leader1 (crash[1] == 1 || leader[1] == expected_leader)
#define elect_leader2 (crash[2] == 1 || leader[2] == expected_leader)
#define elect_leader3 (crash[3] == 1 || leader[3] == expected_leader)
#define elect_same_leader (elect_leader0 && elect_leader1 && elect_leader2 && elect_leader3)
ltl p { []<>elect_same_leader }