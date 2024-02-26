----------------- MODULE leader_election ----------------
EXTENDS TLC, Integers, Sequences

(*--algorithm leader_election

variables
    election_id = [x \in 1..4 |-> 0];
    connected_count = [x \in 1..4 |->3];
    yes_count = [x \in 1..4 |-> 0];
    leader = [x \in 1..4 |-> 0];
    is_crashed = [x \in 1..4 |-> FALSE];
    connected = [x \in 1..4 |-> [y \in 1..4 |-> TRUE]];
    timeout = [x \in 1..4 |-> FALSE];

    \* 0 -> init, 1 -> in election, 2 -> election finished
    state = [x \in 1..4 |-> 0];

    \* queues
    election_messages = [x \in 1..4 |-> <<>>];
    reply_messages = [x \in 1..4 |-> <<>>];
    leader_messages = [x \in 1..4 |-> <<>>];

    lock = TRUE;
    expected_leader = 0;

    msg1;
    msg2;
    msg3;
    msg4;

    reply_message;
    reply_in_massage;
    leader_message;
    node_id_in_message;
    election_id_in_message;

macro set_msg1(from, messages, message) begin
    if from /= 1 /\ connected[from][1] then
        msg1 := Append(messages[1], message);
    else
        msg1 := messages[1];
    end if;
end macro;

macro set_msg2(from, messages, message) begin
    if from /= 2 /\ connected[from][2] then
        msg2 := Append(messages[2], message);
    else
        msg2 := messages[2];
    end if;
end macro;

macro set_msg3(from, messages, message) begin
    if from /= 3 /\ connected[from][3] then
        msg3 := Append(messages[3], message);
    else
        msg3 := messages[3];
    end if;
end macro;

macro set_msg4(from, messages, message) begin
    if from /= 4 /\ connected[from][4] then
        msg4 := Append(messages[4], message);
    else
        msg4 := messages[4];
    end if;
end macro;

\* function for sending election messages to all nodes
macro send_election_message_to_all(node_id, message) begin
    set_msg1(node_id, election_messages, message);
    set_msg2(node_id, election_messages, message);
    set_msg3(node_id, election_messages, message);
    set_msg4(node_id, election_messages, message);
    election_messages := <<msg1, msg2, msg3, msg4>>;
end macro;

\* function for sending leader messages to all nodes
macro send_leader_message_to_all(node_id, message) begin
    set_msg1(node_id, leader_messages, message);
    set_msg2(node_id, leader_messages, message);
    set_msg3(node_id, leader_messages, message);
    set_msg4(node_id, leader_messages, message);
    leader_messages := <<msg1, msg2, msg3, msg4>>;
end macro;

\* function for checking reply messages
macro check_reply_message(node_id) begin
    reply_message := Head(reply_messages[node_id]);
    reply_messages[node_id] := Tail(reply_messages[node_id]);
    reply_in_massage := reply_message.yes;
    election_id_in_message := reply_message.election_id;

    \* if election_id is the same and the reply is YES, increment YES count
    if election_id_in_message = election_id[node_id] /\ reply_in_massage then
        yes_count[node_id] := yes_count[node_id] + 1;

        \* if YES count increses to connected_count, send leader message to all nodes
        if yes_count[node_id] = connected_count[node_id] then
            state[node_id] := 2;
            leader[node_id] := node_id;
            send_leader_message_to_all(node_id,
                [node_id |-> node_id,
                election_id |-> election_id[node_id]])
        end if;
    end if;
end macro;

\* function for checking leader messages
macro check_leader_message(node_id) begin
    leader_message := Head(leader_messages[node_id]);
    leader_messages[node_id] := Tail(leader_messages[node_id]);
    node_id_in_message := leader_message.node_id;
    election_id_in_message := leader_message.election_id;

    \* if election_id is the same, update the leader
    if election_id_in_message = election_id[node_id] then
        state[node_id] := 2;
        leader[node_id] := node_id_in_message;
    end if;
end macro;

\* function for checking timeout
macro check_timeout(node_id) begin
    timeout[node_id] := FALSE;
    connected_count[node_id] := connected_count[node_id] - 1;
    election_id[node_id] := election_id[node_id] + 1;
        
    yes_count[node_id] := 0;
    state[node_id] := 1;
    send_election_message_to_all(node_id,
        [node_id |-> node_id,
        connected_count |-> connected_count[node_id],
        election_id |-> election_id[node_id]]);
end macro;

\* function for starting election
procedure new_election(node_id) begin
    start_new_election:
        yes_count[node_id] := 0;
        state[node_id] := 1;
        send_election_message_to_all(node_id,
            [node_id |-> node_id,
            connected_count |-> connected_count[node_id],
            election_id |-> election_id[node_id]]);

        return;
end procedure;

\* function for checking election messages
procedure check_election_message(node_id)
variables
    election_message,
    connected_count_in_message,
begin
    start_check_election_message:
        election_message := Head(election_messages[node_id]);
        election_messages[node_id] := Tail(election_messages[node_id]);
        node_id_in_message := election_message.node_id;
        connected_count_in_message := election_message.connected_count;
        election_id_in_message := election_message.election_id;

        \* if election_id in msg is bigger than mine, start new election
        if election_id_in_message > election_id[node_id] then
            election_id[node_id] := election_id_in_message;
            call new_election(node_id);

        \* if election_id in msg the same as mine, send reply message
        elsif election_id_in_message = election_id[node_id] then
            if connected_count_in_message > connected_count[node_id] then
                \* reply Yes
                reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                    [yes |-> TRUE, election_id |-> election_id[node_id]]);
            elsif connected_count_in_message = connected_count[node_id] then
                if node_id_in_message < node_id then
                    \* reply Yes
                    reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                        [yes |-> TRUE, election_id |-> election_id[node_id]]);
                elsif node_id_in_message = node_id then
                    \* do nothing. it's my own message
                else
                    \* reply No
                    reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                        [yes |-> FALSE, election_id |-> election_id[node_id]]);
                 end if;
            else
                \* reply No
                reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                    [yes |-> FALSE, election_id |-> election_id[node_id]]);
            end if;
        else
            \* do nothing
        end if;

    end_check_election_message:
        return;
end procedure;

procedure run(node_id)
begin
    init_run:
        connected[node_id][node_id] := FALSE;
    
    check_crash:
        if is_crashed[node_id] then
            return;
        end if;

    check_finish:
        if \A id \in 1..4: (
            is_crashed[id]
            \/ (state[id] = 2
                /\ timeout[id] = FALSE
                /\ election_messages[id] = <<>>
                /\ reply_messages[id] = <<>>
                /\ leader_messages[id] = <<>>)) then
            assert(leader[node_id] = expected_leader);
            return;
        end if;

    \* represent non-deterministic execution
    aquire_lock_and_execute:
        either
            await timeout[node_id];
            await ~lock;
            lock := TRUE;
            check_timeout(node_id);
        or
            await election_messages[node_id] /= <<>>;
            await ~lock;
            lock := TRUE;
            call check_election_message(node_id);
        or
            await reply_messages[node_id] /= <<>>;
            await ~lock;
            lock := TRUE;
            check_reply_message(node_id);
        or
            await leader_messages[node_id] /= <<>>;
            await ~lock;
            lock := TRUE;
            check_leader_message(node_id);
        end either;

    release_lock:
        lock := FALSE;
        goto check_finish;
end procedure;

\* Process 1..4 represent the nodes.
\* Process 5 represents dummy process which invoke node or link crashes.
\* Please initialize is_crashed, timeout, expected_leader and connected variables manually.
fair process N \in 1..5
begin
    start_process:
        if self = 5 then
            \* Node 1 crash
            is_crashed[1] := TRUE;
            timeout := <<FALSE, TRUE, TRUE, TRUE>>;
            expected_leader := 2;
            connected := <<
                <<FALSE, FALSE, FALSE, FALSE>>,
                <<FALSE, FALSE, TRUE, TRUE>>,
                <<FALSE, TRUE, FALSE, TRUE>>,
                <<FALSE, TRUE, TRUE, FALSE>>
            >>;
            \* either
            \*     \* Node 1 crash
            \*     is_crashed[1] := TRUE;
            \*     timeout := <<FALSE, TRUE, TRUE, TRUE>>;
            \*     expected_leader := 2;
            \*     connected := <<
            \*         <<FALSE, FALSE, FALSE, FALSE>>,
            \*         <<FALSE, FALSE, TRUE, TRUE>>,
            \*         <<FALSE, TRUE, FALSE, TRUE>>,
            \*         <<FALSE, TRUE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Node 2 crash
            \*     is_crashed[2] := TRUE;
            \*     timeout := <<TRUE, FALSE, TRUE, TRUE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, FALSE, TRUE, TRUE>>,
            \*         <<FALSE, FALSE, FALSE, FALSE>>,
            \*         <<TRUE, FALSE, FALSE, TRUE>>,
            \*         <<TRUE, FALSE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Node 3 crash
            \*     is_crashed[3] := TRUE;
            \*     timeout := <<TRUE, TRUE, FALSE, TRUE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, TRUE, FALSE, TRUE>>,
            \*         <<TRUE, FALSE, FALSE, TRUE>>,
            \*         <<FALSE, FALSE, FALSE, FALSE>>,
            \*         <<TRUE, TRUE, FALSE, FALSE>>
            \*     >>;
            \* or
            \*     \* Node 4 crash
            \*     is_crashed[4] := TRUE;
            \*     timeout := <<TRUE, TRUE, TRUE, FALSE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, TRUE, TRUE, FALSE>>,
            \*         <<TRUE, FALSE, TRUE, FALSE>>,
            \*         <<TRUE, TRUE, FALSE, FALSE>>,
            \*         <<FALSE, FALSE, FALSE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 1-2 crash
            \*     timeout := <<TRUE, TRUE, FALSE, FALSE>>;
            \*     expected_leader := 3;
            \*     connected := <<
            \*         <<FALSE, FALSE, TRUE, TRUE>>,
            \*         <<FALSE, FALSE, TRUE, TRUE>>,
            \*         <<TRUE, TRUE, FALSE, TRUE>>,
            \*         <<TRUE, TRUE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 1-3 crash
            \*     timeout := <<TRUE, FALSE, TRUE, FALSE>>;
            \*     expected_leader := 2;
            \*     connected := <<
            \*         <<FALSE, TRUE, FALSE, TRUE>>,
            \*         <<TRUE, FALSE, TRUE, TRUE>>,
            \*         <<FALSE, TRUE, FALSE, TRUE>>,
            \*         <<TRUE, TRUE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 1-4 crash
            \*     timeout := <<TRUE, FALSE, FALSE, TRUE>>;
            \*     expected_leader := 2;
            \*     connected := <<
            \*         <<FALSE, TRUE, TRUE, FALSE>>,
            \*         <<TRUE, FALSE, TRUE, TRUE>>,
            \*         <<TRUE, TRUE, FALSE, TRUE>>,
            \*         <<FALSE, TRUE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 2-3 crash
            \*     timeout := <<FALSE, TRUE, TRUE, FALSE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, TRUE, TRUE, TRUE>>,
            \*         <<TRUE, FALSE, FALSE, TRUE>>,
            \*         <<TRUE, FALSE, FALSE, TRUE>>,
            \*         <<TRUE, TRUE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 2-4 crash
            \*     timeout := <<FALSE, TRUE, FALSE, TRUE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, TRUE, TRUE, TRUE>>,
            \*         <<TRUE, FALSE, TRUE, FALSE>>,
            \*         <<TRUE, TRUE, FALSE, TRUE>>,
            \*         <<TRUE, FALSE, TRUE, FALSE>>
            \*     >>;
            \* or
            \*     \* Link 3-4 crash
            \*     timeout := <<FALSE, FALSE, TRUE, TRUE>>;
            \*     expected_leader := 1;
            \*     connected := <<
            \*         <<FALSE, TRUE, TRUE, TRUE>>,
            \*         <<TRUE, FALSE, TRUE, TRUE>>,
            \*         <<TRUE, TRUE, FALSE, FALSE>>,
            \*         <<TRUE, TRUE, FALSE, FALSE>>
            \*     >>;
            \* end either;

            lock := FALSE;
        else
            await ~lock;
            call run(self);
        end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "83c7236f" /\ chksum(tla) = "5661962d")
\* Parameter node_id of procedure new_election at line 138 col 24 changed to node_id_
\* Parameter node_id of procedure check_election_message at line 151 col 34 changed to node_id_c
CONSTANT defaultInitValue
VARIABLES election_id, connected_count, yes_count, leader, is_crashed, 
          connected, timeout, state, election_messages, reply_messages, 
          leader_messages, lock, expected_leader, msg1, msg2, msg3, msg4, 
          reply_message, reply_in_massage, leader_message, node_id_in_message, 
          election_id_in_message, pc, stack, node_id_, node_id_c, 
          election_message, connected_count_in_message, node_id

vars == << election_id, connected_count, yes_count, leader, is_crashed, 
           connected, timeout, state, election_messages, reply_messages, 
           leader_messages, lock, expected_leader, msg1, msg2, msg3, msg4, 
           reply_message, reply_in_massage, leader_message, 
           node_id_in_message, election_id_in_message, pc, stack, node_id_, 
           node_id_c, election_message, connected_count_in_message, node_id
        >>

ProcSet == (1..5)

Init == (* Global variables *)
        /\ election_id = [x \in 1..4 |-> 0]
        /\ connected_count = [x \in 1..4 |->3]
        /\ yes_count = [x \in 1..4 |-> 0]
        /\ leader = [x \in 1..4 |-> 0]
        /\ is_crashed = [x \in 1..4 |-> FALSE]
        /\ connected = [x \in 1..4 |-> [y \in 1..4 |-> TRUE]]
        /\ timeout = [x \in 1..4 |-> FALSE]
        /\ state = [x \in 1..4 |-> 0]
        /\ election_messages = [x \in 1..4 |-> <<>>]
        /\ reply_messages = [x \in 1..4 |-> <<>>]
        /\ leader_messages = [x \in 1..4 |-> <<>>]
        /\ lock = TRUE
        /\ expected_leader = 0
        /\ msg1 = defaultInitValue
        /\ msg2 = defaultInitValue
        /\ msg3 = defaultInitValue
        /\ msg4 = defaultInitValue
        /\ reply_message = defaultInitValue
        /\ reply_in_massage = defaultInitValue
        /\ leader_message = defaultInitValue
        /\ node_id_in_message = defaultInitValue
        /\ election_id_in_message = defaultInitValue
        (* Procedure new_election *)
        /\ node_id_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_election_message *)
        /\ node_id_c = [ self \in ProcSet |-> defaultInitValue]
        /\ election_message = [ self \in ProcSet |-> defaultInitValue]
        /\ connected_count_in_message = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure run *)
        /\ node_id = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_process"]

start_new_election(self) == /\ pc[self] = "start_new_election"
                            /\ yes_count' = [yes_count EXCEPT ![node_id_[self]] = 0]
                            /\ state' = [state EXCEPT ![node_id_[self]] = 1]
                            /\ IF node_id_[self] /= 1 /\ connected[node_id_[self]][1]
                                  THEN /\ msg1' = Append(election_messages[1], ([node_id |-> node_id_[self],
                                                                                connected_count |-> connected_count[node_id_[self]],
                                                                                election_id |-> election_id[node_id_[self]]]))
                                  ELSE /\ msg1' = election_messages[1]
                            /\ IF node_id_[self] /= 2 /\ connected[node_id_[self]][2]
                                  THEN /\ msg2' = Append(election_messages[2], ([node_id |-> node_id_[self],
                                                                                connected_count |-> connected_count[node_id_[self]],
                                                                                election_id |-> election_id[node_id_[self]]]))
                                  ELSE /\ msg2' = election_messages[2]
                            /\ IF node_id_[self] /= 3 /\ connected[node_id_[self]][3]
                                  THEN /\ msg3' = Append(election_messages[3], ([node_id |-> node_id_[self],
                                                                                connected_count |-> connected_count[node_id_[self]],
                                                                                election_id |-> election_id[node_id_[self]]]))
                                  ELSE /\ msg3' = election_messages[3]
                            /\ IF node_id_[self] /= 4 /\ connected[node_id_[self]][4]
                                  THEN /\ msg4' = Append(election_messages[4], ([node_id |-> node_id_[self],
                                                                                connected_count |-> connected_count[node_id_[self]],
                                                                                election_id |-> election_id[node_id_[self]]]))
                                  ELSE /\ msg4' = election_messages[4]
                            /\ election_messages' = <<msg1', msg2', msg3', msg4'>>
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ node_id_' = [node_id_ EXCEPT ![self] = Head(stack[self]).node_id_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << election_id, connected_count, 
                                            leader, is_crashed, connected, 
                                            timeout, reply_messages, 
                                            leader_messages, lock, 
                                            expected_leader, reply_message, 
                                            reply_in_massage, leader_message, 
                                            node_id_in_message, 
                                            election_id_in_message, node_id_c, 
                                            election_message, 
                                            connected_count_in_message, 
                                            node_id >>

new_election(self) == start_new_election(self)

start_check_election_message(self) == /\ pc[self] = "start_check_election_message"
                                      /\ election_message' = [election_message EXCEPT ![self] = Head(election_messages[node_id_c[self]])]
                                      /\ election_messages' = [election_messages EXCEPT ![node_id_c[self]] = Tail(election_messages[node_id_c[self]])]
                                      /\ node_id_in_message' = election_message'[self].node_id
                                      /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = election_message'[self].connected_count]
                                      /\ election_id_in_message' = election_message'[self].election_id
                                      /\ IF election_id_in_message' > election_id[node_id_c[self]]
                                            THEN /\ election_id' = [election_id EXCEPT ![node_id_c[self]] = election_id_in_message']
                                                 /\ /\ node_id_' = [node_id_ EXCEPT ![self] = node_id_c[self]]
                                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "new_election",
                                                                                             pc        |->  "end_check_election_message",
                                                                                             node_id_  |->  node_id_[self] ] >>
                                                                                         \o stack[self]]
                                                 /\ pc' = [pc EXCEPT ![self] = "start_new_election"]
                                                 /\ UNCHANGED reply_messages
                                            ELSE /\ IF election_id_in_message' = election_id[node_id_c[self]]
                                                       THEN /\ IF connected_count_in_message'[self] > connected_count[node_id_c[self]]
                                                                  THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                            [yes |-> TRUE, election_id |-> election_id[node_id_c[self]]])]
                                                                  ELSE /\ IF connected_count_in_message'[self] = connected_count[node_id_c[self]]
                                                                             THEN /\ IF node_id_in_message' < node_id_c[self]
                                                                                        THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                                                  [yes |-> TRUE, election_id |-> election_id[node_id_c[self]]])]
                                                                                        ELSE /\ IF node_id_in_message' = node_id_c[self]
                                                                                                   THEN /\ UNCHANGED reply_messages
                                                                                                   ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                                                             [yes |-> FALSE, election_id |-> election_id[node_id_c[self]]])]
                                                                             ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                                       [yes |-> FALSE, election_id |-> election_id[node_id_c[self]]])]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED reply_messages
                                                 /\ pc' = [pc EXCEPT ![self] = "end_check_election_message"]
                                                 /\ UNCHANGED << election_id, 
                                                                 stack, 
                                                                 node_id_ >>
                                      /\ UNCHANGED << connected_count, 
                                                      yes_count, leader, 
                                                      is_crashed, connected, 
                                                      timeout, state, 
                                                      leader_messages, lock, 
                                                      expected_leader, msg1, 
                                                      msg2, msg3, msg4, 
                                                      reply_message, 
                                                      reply_in_massage, 
                                                      leader_message, 
                                                      node_id_c, node_id >>

end_check_election_message(self) == /\ pc[self] = "end_check_election_message"
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ election_message' = [election_message EXCEPT ![self] = Head(stack[self]).election_message]
                                    /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = Head(stack[self]).connected_count_in_message]
                                    /\ node_id_c' = [node_id_c EXCEPT ![self] = Head(stack[self]).node_id_c]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED << election_id, 
                                                    connected_count, yes_count, 
                                                    leader, is_crashed, 
                                                    connected, timeout, state, 
                                                    election_messages, 
                                                    reply_messages, 
                                                    leader_messages, lock, 
                                                    expected_leader, msg1, 
                                                    msg2, msg3, msg4, 
                                                    reply_message, 
                                                    reply_in_massage, 
                                                    leader_message, 
                                                    node_id_in_message, 
                                                    election_id_in_message, 
                                                    node_id_, node_id >>

check_election_message(self) == start_check_election_message(self)
                                   \/ end_check_election_message(self)

init_run(self) == /\ pc[self] = "init_run"
                  /\ connected' = [connected EXCEPT ![node_id[self]][node_id[self]] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "check_crash"]
                  /\ UNCHANGED << election_id, connected_count, yes_count, 
                                  leader, is_crashed, timeout, state, 
                                  election_messages, reply_messages, 
                                  leader_messages, lock, expected_leader, msg1, 
                                  msg2, msg3, msg4, reply_message, 
                                  reply_in_massage, leader_message, 
                                  node_id_in_message, election_id_in_message, 
                                  stack, node_id_, node_id_c, election_message, 
                                  connected_count_in_message, node_id >>

check_crash(self) == /\ pc[self] = "check_crash"
                     /\ IF is_crashed[node_id[self]]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ node_id' = [node_id EXCEPT ![self] = Head(stack[self]).node_id]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "check_finish"]
                                /\ UNCHANGED << stack, node_id >>
                     /\ UNCHANGED << election_id, connected_count, yes_count, 
                                     leader, is_crashed, connected, timeout, 
                                     state, election_messages, reply_messages, 
                                     leader_messages, lock, expected_leader, 
                                     msg1, msg2, msg3, msg4, reply_message, 
                                     reply_in_massage, leader_message, 
                                     node_id_in_message, 
                                     election_id_in_message, node_id_, 
                                     node_id_c, election_message, 
                                     connected_count_in_message >>

check_finish(self) == /\ pc[self] = "check_finish"
                      /\ IF \A id \in 1..4: (
                             is_crashed[id]
                             \/ (state[id] = 2
                                 /\ timeout[id] = FALSE
                                 /\ election_messages[id] = <<>>
                                 /\ reply_messages[id] = <<>>
                                 /\ leader_messages[id] = <<>>))
                            THEN /\ Assert((leader[node_id[self]] = expected_leader), 
                                           "Failure of assertion at line 217, column 13.")
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ node_id' = [node_id EXCEPT ![self] = Head(stack[self]).node_id]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "aquire_lock_and_execute"]
                                 /\ UNCHANGED << stack, node_id >>
                      /\ UNCHANGED << election_id, connected_count, yes_count, 
                                      leader, is_crashed, connected, timeout, 
                                      state, election_messages, reply_messages, 
                                      leader_messages, lock, expected_leader, 
                                      msg1, msg2, msg3, msg4, reply_message, 
                                      reply_in_massage, leader_message, 
                                      node_id_in_message, 
                                      election_id_in_message, node_id_, 
                                      node_id_c, election_message, 
                                      connected_count_in_message >>

aquire_lock_and_execute(self) == /\ pc[self] = "aquire_lock_and_execute"
                                 /\ \/ /\ timeout[node_id[self]]
                                       /\ ~lock
                                       /\ lock' = TRUE
                                       /\ timeout' = [timeout EXCEPT ![node_id[self]] = FALSE]
                                       /\ connected_count' = [connected_count EXCEPT ![node_id[self]] = connected_count[node_id[self]] - 1]
                                       /\ election_id' = [election_id EXCEPT ![node_id[self]] = election_id[node_id[self]] + 1]
                                       /\ yes_count' = [yes_count EXCEPT ![node_id[self]] = 0]
                                       /\ state' = [state EXCEPT ![node_id[self]] = 1]
                                       /\ IF node_id[self] /= 1 /\ connected[node_id[self]][1]
                                             THEN /\ msg1' = Append(election_messages[1], ([node_id |-> node_id[self],
                                                                                           connected_count |-> connected_count'[node_id[self]],
                                                                                           election_id |-> election_id'[node_id[self]]]))
                                             ELSE /\ msg1' = election_messages[1]
                                       /\ IF node_id[self] /= 2 /\ connected[node_id[self]][2]
                                             THEN /\ msg2' = Append(election_messages[2], ([node_id |-> node_id[self],
                                                                                           connected_count |-> connected_count'[node_id[self]],
                                                                                           election_id |-> election_id'[node_id[self]]]))
                                             ELSE /\ msg2' = election_messages[2]
                                       /\ IF node_id[self] /= 3 /\ connected[node_id[self]][3]
                                             THEN /\ msg3' = Append(election_messages[3], ([node_id |-> node_id[self],
                                                                                           connected_count |-> connected_count'[node_id[self]],
                                                                                           election_id |-> election_id'[node_id[self]]]))
                                             ELSE /\ msg3' = election_messages[3]
                                       /\ IF node_id[self] /= 4 /\ connected[node_id[self]][4]
                                             THEN /\ msg4' = Append(election_messages[4], ([node_id |-> node_id[self],
                                                                                           connected_count |-> connected_count'[node_id[self]],
                                                                                           election_id |-> election_id'[node_id[self]]]))
                                             ELSE /\ msg4' = election_messages[4]
                                       /\ election_messages' = <<msg1', msg2', msg3', msg4'>>
                                       /\ pc' = [pc EXCEPT ![self] = "release_lock"]
                                       /\ UNCHANGED <<leader, reply_messages, leader_messages, reply_message, reply_in_massage, leader_message, node_id_in_message, election_id_in_message, stack, node_id_c, election_message, connected_count_in_message>>
                                    \/ /\ election_messages[node_id[self]] /= <<>>
                                       /\ ~lock
                                       /\ lock' = TRUE
                                       /\ /\ node_id_c' = [node_id_c EXCEPT ![self] = node_id[self]]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_election_message",
                                                                                   pc        |->  "release_lock",
                                                                                   election_message |->  election_message[self],
                                                                                   connected_count_in_message |->  connected_count_in_message[self],
                                                                                   node_id_c |->  node_id_c[self] ] >>
                                                                               \o stack[self]]
                                       /\ election_message' = [election_message EXCEPT ![self] = defaultInitValue]
                                       /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = defaultInitValue]
                                       /\ pc' = [pc EXCEPT ![self] = "start_check_election_message"]
                                       /\ UNCHANGED <<election_id, connected_count, yes_count, leader, timeout, state, election_messages, reply_messages, leader_messages, msg1, msg2, msg3, msg4, reply_message, reply_in_massage, leader_message, node_id_in_message, election_id_in_message>>
                                    \/ /\ reply_messages[node_id[self]] /= <<>>
                                       /\ ~lock
                                       /\ lock' = TRUE
                                       /\ reply_message' = Head(reply_messages[node_id[self]])
                                       /\ reply_messages' = [reply_messages EXCEPT ![node_id[self]] = Tail(reply_messages[node_id[self]])]
                                       /\ reply_in_massage' = reply_message'.yes
                                       /\ election_id_in_message' = reply_message'.election_id
                                       /\ IF election_id_in_message' = election_id[node_id[self]] /\ reply_in_massage'
                                             THEN /\ yes_count' = [yes_count EXCEPT ![node_id[self]] = yes_count[node_id[self]] + 1]
                                                  /\ IF yes_count'[node_id[self]] = connected_count[node_id[self]]
                                                        THEN /\ state' = [state EXCEPT ![node_id[self]] = 2]
                                                             /\ leader' = [leader EXCEPT ![node_id[self]] = node_id[self]]
                                                             /\ IF node_id[self] /= 1 /\ connected[node_id[self]][1]
                                                                   THEN /\ msg1' = Append(leader_messages[1], ([node_id |-> node_id[self],
                                                                                                               election_id |-> election_id[node_id[self]]]))
                                                                   ELSE /\ msg1' = leader_messages[1]
                                                             /\ IF node_id[self] /= 2 /\ connected[node_id[self]][2]
                                                                   THEN /\ msg2' = Append(leader_messages[2], ([node_id |-> node_id[self],
                                                                                                               election_id |-> election_id[node_id[self]]]))
                                                                   ELSE /\ msg2' = leader_messages[2]
                                                             /\ IF node_id[self] /= 3 /\ connected[node_id[self]][3]
                                                                   THEN /\ msg3' = Append(leader_messages[3], ([node_id |-> node_id[self],
                                                                                                               election_id |-> election_id[node_id[self]]]))
                                                                   ELSE /\ msg3' = leader_messages[3]
                                                             /\ IF node_id[self] /= 4 /\ connected[node_id[self]][4]
                                                                   THEN /\ msg4' = Append(leader_messages[4], ([node_id |-> node_id[self],
                                                                                                               election_id |-> election_id[node_id[self]]]))
                                                                   ELSE /\ msg4' = leader_messages[4]
                                                             /\ leader_messages' = <<msg1', msg2', msg3', msg4'>>
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED << leader, 
                                                                             state, 
                                                                             leader_messages, 
                                                                             msg1, 
                                                                             msg2, 
                                                                             msg3, 
                                                                             msg4 >>
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << yes_count, 
                                                                  leader, 
                                                                  state, 
                                                                  leader_messages, 
                                                                  msg1, msg2, 
                                                                  msg3, msg4 >>
                                       /\ pc' = [pc EXCEPT ![self] = "release_lock"]
                                       /\ UNCHANGED <<election_id, connected_count, timeout, election_messages, leader_message, node_id_in_message, stack, node_id_c, election_message, connected_count_in_message>>
                                    \/ /\ leader_messages[node_id[self]] /= <<>>
                                       /\ ~lock
                                       /\ lock' = TRUE
                                       /\ leader_message' = Head(leader_messages[node_id[self]])
                                       /\ leader_messages' = [leader_messages EXCEPT ![node_id[self]] = Tail(leader_messages[node_id[self]])]
                                       /\ node_id_in_message' = leader_message'.node_id
                                       /\ election_id_in_message' = leader_message'.election_id
                                       /\ IF election_id_in_message' = election_id[node_id[self]]
                                             THEN /\ state' = [state EXCEPT ![node_id[self]] = 2]
                                                  /\ leader' = [leader EXCEPT ![node_id[self]] = node_id_in_message']
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << leader, 
                                                                  state >>
                                       /\ pc' = [pc EXCEPT ![self] = "release_lock"]
                                       /\ UNCHANGED <<election_id, connected_count, yes_count, timeout, election_messages, reply_messages, msg1, msg2, msg3, msg4, reply_message, reply_in_massage, stack, node_id_c, election_message, connected_count_in_message>>
                                 /\ UNCHANGED << is_crashed, connected, 
                                                 expected_leader, node_id_, 
                                                 node_id >>

release_lock(self) == /\ pc[self] = "release_lock"
                      /\ lock' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "check_finish"]
                      /\ UNCHANGED << election_id, connected_count, yes_count, 
                                      leader, is_crashed, connected, timeout, 
                                      state, election_messages, reply_messages, 
                                      leader_messages, expected_leader, msg1, 
                                      msg2, msg3, msg4, reply_message, 
                                      reply_in_massage, leader_message, 
                                      node_id_in_message, 
                                      election_id_in_message, stack, node_id_, 
                                      node_id_c, election_message, 
                                      connected_count_in_message, node_id >>

run(self) == init_run(self) \/ check_crash(self) \/ check_finish(self)
                \/ aquire_lock_and_execute(self) \/ release_lock(self)

start_process(self) == /\ pc[self] = "start_process"
                       /\ IF self = 5
                             THEN /\ is_crashed' = [is_crashed EXCEPT ![1] = TRUE]
                                  /\ timeout' = <<FALSE, TRUE, TRUE, TRUE>>
                                  /\ expected_leader' = 2
                                  /\ connected' =              <<
                                                      <<FALSE, FALSE, FALSE, FALSE>>,
                                                      <<FALSE, FALSE, TRUE, TRUE>>,
                                                      <<FALSE, TRUE, FALSE, TRUE>>,
                                                      <<FALSE, TRUE, TRUE, FALSE>>
                                                  >>
                                  /\ lock' = FALSE
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, node_id >>
                             ELSE /\ ~lock
                                  /\ /\ node_id' = [node_id EXCEPT ![self] = self]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run",
                                                                              pc        |->  "Done",
                                                                              node_id   |->  node_id[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "init_run"]
                                  /\ UNCHANGED << is_crashed, connected, 
                                                  timeout, lock, 
                                                  expected_leader >>
                       /\ UNCHANGED << election_id, connected_count, yes_count, 
                                       leader, state, election_messages, 
                                       reply_messages, leader_messages, msg1, 
                                       msg2, msg3, msg4, reply_message, 
                                       reply_in_massage, leader_message, 
                                       node_id_in_message, 
                                       election_id_in_message, node_id_, 
                                       node_id_c, election_message, 
                                       connected_count_in_message >>

N(self) == start_process(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ new_election(self)
                               \/ check_election_message(self) \/ run(self))
           \/ (\E self \in 1..5: N(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..5 : /\ WF_vars(N(self))
                              /\ WF_vars(run(self))
                              /\ WF_vars(new_election(self))
                              /\ WF_vars(check_election_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
