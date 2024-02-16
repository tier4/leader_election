----------------- MODULE leader_election ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS NODE_NUM

(*--algorithm leader_election

variables
    election_id = [x \in 1..NODE_NUM |-> 0];
    connected_count = [x \in 1..NODE_NUM |-> NODE_NUM - 1];
    yes_count = [x \in 1..NODE_NUM |-> 0];
    leader = [x \in 1..NODE_NUM |-> 0];
    is_crashed = [x \in 1..NODE_NUM |-> FALSE];
    connected = [x \in 1..NODE_NUM |-> [y \in 1..NODE_NUM |-> TRUE]];
    timeout = [x \in 1..NODE_NUM |-> FALSE];

    \* 0 -> init, 1 -> in election, 2 -> election finished
    state = [x \in 1..NODE_NUM |-> 0];

    \* queues
    election_messages = [x \in 1..NODE_NUM |-> <<>>];
    reply_messages = [x \in 1..NODE_NUM |-> <<>>];
    leader_messages = [x \in 1..NODE_NUM |-> <<>>];

    lock = FALSE;

procedure send_election_message_to_all(from_node, to_node, message)
begin
    start_send_election_message:
        if from_node /= to_node /\ connected[from_node][to_node] then
            election_messages[to_node] := Append(election_messages[to_node], message);
        end if;

        if to_node < NODE_NUM then
            send_election_message: call send_election_message_to_all(from_node, to_node + 1, message);
        end if;
    
    end_send_election_message:
        return;
end procedure;

procedure send_leader_message_to_all(from_node, to_node, message)
begin
    start_send_leader_message:
        if from_node /= to_node /\ connected[from_node][to_node] then
            leader_messages[to_node] := Append(leader_messages[to_node], message);
        end if;

        if to_node < NODE_NUM then
            send_leader_message: call send_leader_message_to_all(from_node, to_node + 1, message);
        end if;

    end_send_leader_message:
        return;
end procedure;

procedure new_election(node_id)
begin
    start_new_election:
        yes_count[node_id] := 0;
        state[node_id] := 1;
        call send_election_message_to_all(node_id, 1,
                    [node_id |-> node_id,
                    connected_count |-> connected_count[node_id],
                    election_id |-> election_id[node_id]]);

        return;
end procedure;

procedure check_timeout(node_id)
begin
    start_check_timeout:
        if timeout[node_id] then
            timeout[node_id] := FALSE;
            connected_count[node_id] := connected_count[node_id] - 1;
            election_id[node_id] := election_id[node_id] + 1;
            call new_election(node_id);
        end if;

    end_check_timeout:
        return;
end procedure;

procedure check_election_message(node_id)
variables
    election_message,
    node_id_in_message,
    connected_count_in_message,
    election_id_in_message
begin
    start_check_election_message:
        if election_messages[node_id] /= <<>> then
            election_message := Head(election_messages[node_id]);
            election_messages[node_id] := Tail(election_messages[node_id]);
            node_id_in_message := election_message.node_id;
            connected_count_in_message := election_message.connected_count;
            election_id_in_message := election_message.election_id;

            if election_id_in_message > election_id[node_id] then
                election_id[node_id] := election_id_in_message;
                call new_election(node_id);
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
        end if;

    end_check_election_message:
        return;
end procedure;

procedure check_reply_message(node_id)
variables
    reply_message,
    reply_in_massage,
    election_id_in_message
begin
    start_check_reply_message:
        if reply_messages[node_id] /= <<>> then
            reply_message := Head(reply_messages[node_id]);
            reply_messages[node_id] := Tail(reply_messages[node_id]);
            reply_in_massage := reply_message.yes;
            election_id_in_message := reply_message.election_id;

            if election_id_in_message = election_id[node_id] /\ reply_in_massage then
                yes_count[node_id] := yes_count[node_id] + 1;

                if yes_count[node_id] = connected_count[node_id] then
                    call send_leader_message_to_all(node_id, 1,
                            [node_id |-> node_id,
                            election_id |-> election_id[node_id]])
                end if;
            end if;
        end if;

    end_check_reply_message:
        return;
end procedure;

procedure check_leader_message(node_id)
variables
    leader_message,
    node_id_in_message,
    election_id_in_message
begin
    start_check_leader_message:
        if leader_messages[node_id] /= <<>> then
            leader_message := Head(leader_messages[node_id]);
            leader_messages[node_id] := Tail(leader_messages[node_id]);
            node_id_in_message := leader_message.node_id;
            election_id_in_message := leader_message.election_id;

            if election_id_in_message = election_id[node_id] then
                leader[node_id] := node_id_in_message;
                state[node_id] := 2;
            end if;
        end if;
        
    end_check_leader_message:
        return;
end procedure;

procedure run(node_id)
begin
    init_run:
        connected[node_id][node_id] := FALSE;

    aquire_lock:
        await ~lock;
        lock := TRUE;
    
    check_crash:
        if is_crashed[node_id] then
            lock := FALSE;
            return;
        end if;
    
    check_finish:
        if \A id \in 1..NODE_NUM: (is_crashed[id]
                                   \/ (state[id] = 2
                                       /\ election_messages[id] = <<>>
                                       /\ reply_messages[id] = <<>>
                                       /\ leader_messages[id] = <<>>)) then
            lock := FALSE;
            assert(leader[node_id] = 1);
            return;
        end if;

    start_run:
        either
            call check_timeout(node_id);
        or
            call check_election_message(node_id);
        or
            call check_reply_message(node_id);
        or
            call check_leader_message(node_id);
        end either;

    release_lock:
        lock := FALSE;
        goto aquire_lock;
end procedure;

fair+ process N \in 1..NODE_NUM+1
begin
    start_process:
        if self = NODE_NUM+1 then
            \* Node 1 Crash
            is_crashed[1] := TRUE;
            timeout := <<FALSE, TRUE, TRUE, TRUE>>;
            connected := <<
                <<FALSE, FALSE, FALSE, FALSE>>,
                <<FALSE, FALSE, TRUE,  TRUE>>,
                <<FALSE, TRUE,  FALSE, TRUE>>,
                <<FALSE, TRUE,  TRUE,  FALSE>>
            >>
        else
            call run(self);
        end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3168cd13" /\ chksum(tla) = "4b72e629")
\* Procedure variable node_id_in_message of procedure check_election_message at line 87 col 5 changed to node_id_in_message_
\* Procedure variable election_id_in_message of procedure check_election_message at line 89 col 5 changed to election_id_in_message_
\* Procedure variable election_id_in_message of procedure check_reply_message at line 137 col 5 changed to election_id_in_message_c
\* Parameter from_node of procedure send_election_message_to_all at line 27 col 40 changed to from_node_
\* Parameter to_node of procedure send_election_message_to_all at line 27 col 51 changed to to_node_
\* Parameter message of procedure send_election_message_to_all at line 27 col 60 changed to message_
\* Parameter node_id of procedure new_election at line 57 col 24 changed to node_id_
\* Parameter node_id of procedure check_timeout at line 70 col 25 changed to node_id_c
\* Parameter node_id of procedure check_election_message at line 84 col 34 changed to node_id_ch
\* Parameter node_id of procedure check_reply_message at line 133 col 31 changed to node_id_che
\* Parameter node_id of procedure check_leader_message at line 161 col 32 changed to node_id_chec
CONSTANT defaultInitValue
VARIABLES election_id, connected_count, yes_count, leader, is_crashed, 
          connected, timeout, state, election_messages, reply_messages, 
          leader_messages, lock, pc, stack, from_node_, to_node_, message_, 
          from_node, to_node, message, node_id_, node_id_c, node_id_ch, 
          election_message, node_id_in_message_, connected_count_in_message, 
          election_id_in_message_, node_id_che, reply_message, 
          reply_in_massage, election_id_in_message_c, node_id_chec, 
          leader_message, node_id_in_message, election_id_in_message, node_id

vars == << election_id, connected_count, yes_count, leader, is_crashed, 
           connected, timeout, state, election_messages, reply_messages, 
           leader_messages, lock, pc, stack, from_node_, to_node_, message_, 
           from_node, to_node, message, node_id_, node_id_c, node_id_ch, 
           election_message, node_id_in_message_, connected_count_in_message, 
           election_id_in_message_, node_id_che, reply_message, 
           reply_in_massage, election_id_in_message_c, node_id_chec, 
           leader_message, node_id_in_message, election_id_in_message, 
           node_id >>

ProcSet == (1..NODE_NUM+1)

Init == (* Global variables *)
        /\ election_id = [x \in 1..NODE_NUM |-> 0]
        /\ connected_count = [x \in 1..NODE_NUM |-> NODE_NUM - 1]
        /\ yes_count = [x \in 1..NODE_NUM |-> 0]
        /\ leader = [x \in 1..NODE_NUM |-> 0]
        /\ is_crashed = [x \in 1..NODE_NUM |-> FALSE]
        /\ connected = [x \in 1..NODE_NUM |-> [y \in 1..NODE_NUM |-> TRUE]]
        /\ timeout = [x \in 1..NODE_NUM |-> FALSE]
        /\ state = [x \in 1..NODE_NUM |-> 0]
        /\ election_messages = [x \in 1..NODE_NUM |-> <<>>]
        /\ reply_messages = [x \in 1..NODE_NUM |-> <<>>]
        /\ leader_messages = [x \in 1..NODE_NUM |-> <<>>]
        /\ lock = FALSE
        (* Procedure send_election_message_to_all *)
        /\ from_node_ = [ self \in ProcSet |-> defaultInitValue]
        /\ to_node_ = [ self \in ProcSet |-> defaultInitValue]
        /\ message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure send_leader_message_to_all *)
        /\ from_node = [ self \in ProcSet |-> defaultInitValue]
        /\ to_node = [ self \in ProcSet |-> defaultInitValue]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure new_election *)
        /\ node_id_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_timeout *)
        /\ node_id_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_election_message *)
        /\ node_id_ch = [ self \in ProcSet |-> defaultInitValue]
        /\ election_message = [ self \in ProcSet |-> defaultInitValue]
        /\ node_id_in_message_ = [ self \in ProcSet |-> defaultInitValue]
        /\ connected_count_in_message = [ self \in ProcSet |-> defaultInitValue]
        /\ election_id_in_message_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_reply_message *)
        /\ node_id_che = [ self \in ProcSet |-> defaultInitValue]
        /\ reply_message = [ self \in ProcSet |-> defaultInitValue]
        /\ reply_in_massage = [ self \in ProcSet |-> defaultInitValue]
        /\ election_id_in_message_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure check_leader_message *)
        /\ node_id_chec = [ self \in ProcSet |-> defaultInitValue]
        /\ leader_message = [ self \in ProcSet |-> defaultInitValue]
        /\ node_id_in_message = [ self \in ProcSet |-> defaultInitValue]
        /\ election_id_in_message = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure run *)
        /\ node_id = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_process"]

start_send_election_message(self) == /\ pc[self] = "start_send_election_message"
                                     /\ IF from_node_[self] /= to_node_[self] /\ connected[from_node_[self]][to_node_[self]]
                                           THEN /\ election_messages' = [election_messages EXCEPT ![to_node_[self]] = Append(election_messages[to_node_[self]], message_[self])]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED election_messages
                                     /\ IF to_node_[self] < NODE_NUM
                                           THEN /\ pc' = [pc EXCEPT ![self] = "send_election_message"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "end_send_election_message"]
                                     /\ UNCHANGED << election_id, 
                                                     connected_count, 
                                                     yes_count, leader, 
                                                     is_crashed, connected, 
                                                     timeout, state, 
                                                     reply_messages, 
                                                     leader_messages, lock, 
                                                     stack, from_node_, 
                                                     to_node_, message_, 
                                                     from_node, to_node, 
                                                     message, node_id_, 
                                                     node_id_c, node_id_ch, 
                                                     election_message, 
                                                     node_id_in_message_, 
                                                     connected_count_in_message, 
                                                     election_id_in_message_, 
                                                     node_id_che, 
                                                     reply_message, 
                                                     reply_in_massage, 
                                                     election_id_in_message_c, 
                                                     node_id_chec, 
                                                     leader_message, 
                                                     node_id_in_message, 
                                                     election_id_in_message, 
                                                     node_id >>

send_election_message(self) == /\ pc[self] = "send_election_message"
                               /\ /\ from_node_' = [from_node_ EXCEPT ![self] = from_node_[self]]
                                  /\ message_' = [message_ EXCEPT ![self] = message_[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_election_message_to_all",
                                                                           pc        |->  "end_send_election_message",
                                                                           from_node_ |->  from_node_[self],
                                                                           to_node_  |->  to_node_[self],
                                                                           message_  |->  message_[self] ] >>
                                                                       \o stack[self]]
                                  /\ to_node_' = [to_node_ EXCEPT ![self] = to_node_[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "start_send_election_message"]
                               /\ UNCHANGED << election_id, connected_count, 
                                               yes_count, leader, is_crashed, 
                                               connected, timeout, state, 
                                               election_messages, 
                                               reply_messages, leader_messages, 
                                               lock, from_node, to_node, 
                                               message, node_id_, node_id_c, 
                                               node_id_ch, election_message, 
                                               node_id_in_message_, 
                                               connected_count_in_message, 
                                               election_id_in_message_, 
                                               node_id_che, reply_message, 
                                               reply_in_massage, 
                                               election_id_in_message_c, 
                                               node_id_chec, leader_message, 
                                               node_id_in_message, 
                                               election_id_in_message, node_id >>

end_send_election_message(self) == /\ pc[self] = "end_send_election_message"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ from_node_' = [from_node_ EXCEPT ![self] = Head(stack[self]).from_node_]
                                   /\ to_node_' = [to_node_ EXCEPT ![self] = Head(stack[self]).to_node_]
                                   /\ message_' = [message_ EXCEPT ![self] = Head(stack[self]).message_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << election_id, 
                                                   connected_count, yes_count, 
                                                   leader, is_crashed, 
                                                   connected, timeout, state, 
                                                   election_messages, 
                                                   reply_messages, 
                                                   leader_messages, lock, 
                                                   from_node, to_node, message, 
                                                   node_id_, node_id_c, 
                                                   node_id_ch, 
                                                   election_message, 
                                                   node_id_in_message_, 
                                                   connected_count_in_message, 
                                                   election_id_in_message_, 
                                                   node_id_che, reply_message, 
                                                   reply_in_massage, 
                                                   election_id_in_message_c, 
                                                   node_id_chec, 
                                                   leader_message, 
                                                   node_id_in_message, 
                                                   election_id_in_message, 
                                                   node_id >>

send_election_message_to_all(self) == start_send_election_message(self)
                                         \/ send_election_message(self)
                                         \/ end_send_election_message(self)

start_send_leader_message(self) == /\ pc[self] = "start_send_leader_message"
                                   /\ IF from_node[self] /= to_node[self] /\ connected[from_node[self]][to_node[self]]
                                         THEN /\ leader_messages' = [leader_messages EXCEPT ![to_node[self]] = Append(leader_messages[to_node[self]], message[self])]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED leader_messages
                                   /\ IF to_node[self] < NODE_NUM
                                         THEN /\ pc' = [pc EXCEPT ![self] = "send_leader_message"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "end_send_leader_message"]
                                   /\ UNCHANGED << election_id, 
                                                   connected_count, yes_count, 
                                                   leader, is_crashed, 
                                                   connected, timeout, state, 
                                                   election_messages, 
                                                   reply_messages, lock, stack, 
                                                   from_node_, to_node_, 
                                                   message_, from_node, 
                                                   to_node, message, node_id_, 
                                                   node_id_c, node_id_ch, 
                                                   election_message, 
                                                   node_id_in_message_, 
                                                   connected_count_in_message, 
                                                   election_id_in_message_, 
                                                   node_id_che, reply_message, 
                                                   reply_in_massage, 
                                                   election_id_in_message_c, 
                                                   node_id_chec, 
                                                   leader_message, 
                                                   node_id_in_message, 
                                                   election_id_in_message, 
                                                   node_id >>

send_leader_message(self) == /\ pc[self] = "send_leader_message"
                             /\ /\ from_node' = [from_node EXCEPT ![self] = from_node[self]]
                                /\ message' = [message EXCEPT ![self] = message[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_leader_message_to_all",
                                                                         pc        |->  "end_send_leader_message",
                                                                         from_node |->  from_node[self],
                                                                         to_node   |->  to_node[self],
                                                                         message   |->  message[self] ] >>
                                                                     \o stack[self]]
                                /\ to_node' = [to_node EXCEPT ![self] = to_node[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "start_send_leader_message"]
                             /\ UNCHANGED << election_id, connected_count, 
                                             yes_count, leader, is_crashed, 
                                             connected, timeout, state, 
                                             election_messages, reply_messages, 
                                             leader_messages, lock, from_node_, 
                                             to_node_, message_, node_id_, 
                                             node_id_c, node_id_ch, 
                                             election_message, 
                                             node_id_in_message_, 
                                             connected_count_in_message, 
                                             election_id_in_message_, 
                                             node_id_che, reply_message, 
                                             reply_in_massage, 
                                             election_id_in_message_c, 
                                             node_id_chec, leader_message, 
                                             node_id_in_message, 
                                             election_id_in_message, node_id >>

end_send_leader_message(self) == /\ pc[self] = "end_send_leader_message"
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ from_node' = [from_node EXCEPT ![self] = Head(stack[self]).from_node]
                                 /\ to_node' = [to_node EXCEPT ![self] = Head(stack[self]).to_node]
                                 /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << election_id, connected_count, 
                                                 yes_count, leader, is_crashed, 
                                                 connected, timeout, state, 
                                                 election_messages, 
                                                 reply_messages, 
                                                 leader_messages, lock, 
                                                 from_node_, to_node_, 
                                                 message_, node_id_, node_id_c, 
                                                 node_id_ch, election_message, 
                                                 node_id_in_message_, 
                                                 connected_count_in_message, 
                                                 election_id_in_message_, 
                                                 node_id_che, reply_message, 
                                                 reply_in_massage, 
                                                 election_id_in_message_c, 
                                                 node_id_chec, leader_message, 
                                                 node_id_in_message, 
                                                 election_id_in_message, 
                                                 node_id >>

send_leader_message_to_all(self) == start_send_leader_message(self)
                                       \/ send_leader_message(self)
                                       \/ end_send_leader_message(self)

start_new_election(self) == /\ pc[self] = "start_new_election"
                            /\ yes_count' = [yes_count EXCEPT ![node_id_[self]] = 0]
                            /\ state' = [state EXCEPT ![node_id_[self]] = 1]
                            /\ /\ from_node_' = [from_node_ EXCEPT ![self] = node_id_[self]]
                               /\ message_' = [message_ EXCEPT ![self] = [node_id |-> node_id_[self],
                                                                         connected_count |-> connected_count[node_id_[self]],
                                                                         election_id |-> election_id[node_id_[self]]]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_election_message_to_all",
                                                                        pc        |->  Head(stack[self]).pc,
                                                                        from_node_ |->  from_node_[self],
                                                                        to_node_  |->  to_node_[self],
                                                                        message_  |->  message_[self] ] >>
                                                                    \o Tail(stack[self])]
                               /\ to_node_' = [to_node_ EXCEPT ![self] = 1]
                            /\ pc' = [pc EXCEPT ![self] = "start_send_election_message"]
                            /\ UNCHANGED << election_id, connected_count, 
                                            leader, is_crashed, connected, 
                                            timeout, election_messages, 
                                            reply_messages, leader_messages, 
                                            lock, from_node, to_node, message, 
                                            node_id_, node_id_c, node_id_ch, 
                                            election_message, 
                                            node_id_in_message_, 
                                            connected_count_in_message, 
                                            election_id_in_message_, 
                                            node_id_che, reply_message, 
                                            reply_in_massage, 
                                            election_id_in_message_c, 
                                            node_id_chec, leader_message, 
                                            node_id_in_message, 
                                            election_id_in_message, node_id >>

new_election(self) == start_new_election(self)

start_check_timeout(self) == /\ pc[self] = "start_check_timeout"
                             /\ IF timeout[node_id_c[self]]
                                   THEN /\ timeout' = [timeout EXCEPT ![node_id_c[self]] = FALSE]
                                        /\ connected_count' = [connected_count EXCEPT ![node_id_c[self]] = connected_count[node_id_c[self]] - 1]
                                        /\ election_id' = [election_id EXCEPT ![node_id_c[self]] = election_id[node_id_c[self]] + 1]
                                        /\ /\ node_id_' = [node_id_ EXCEPT ![self] = node_id_c[self]]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "new_election",
                                                                                    pc        |->  "end_check_timeout",
                                                                                    node_id_  |->  node_id_[self] ] >>
                                                                                \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "start_new_election"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "end_check_timeout"]
                                        /\ UNCHANGED << election_id, 
                                                        connected_count, 
                                                        timeout, stack, 
                                                        node_id_ >>
                             /\ UNCHANGED << yes_count, leader, is_crashed, 
                                             connected, state, 
                                             election_messages, reply_messages, 
                                             leader_messages, lock, from_node_, 
                                             to_node_, message_, from_node, 
                                             to_node, message, node_id_c, 
                                             node_id_ch, election_message, 
                                             node_id_in_message_, 
                                             connected_count_in_message, 
                                             election_id_in_message_, 
                                             node_id_che, reply_message, 
                                             reply_in_massage, 
                                             election_id_in_message_c, 
                                             node_id_chec, leader_message, 
                                             node_id_in_message, 
                                             election_id_in_message, node_id >>

end_check_timeout(self) == /\ pc[self] = "end_check_timeout"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ node_id_c' = [node_id_c EXCEPT ![self] = Head(stack[self]).node_id_c]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << election_id, connected_count, 
                                           yes_count, leader, is_crashed, 
                                           connected, timeout, state, 
                                           election_messages, reply_messages, 
                                           leader_messages, lock, from_node_, 
                                           to_node_, message_, from_node, 
                                           to_node, message, node_id_, 
                                           node_id_ch, election_message, 
                                           node_id_in_message_, 
                                           connected_count_in_message, 
                                           election_id_in_message_, 
                                           node_id_che, reply_message, 
                                           reply_in_massage, 
                                           election_id_in_message_c, 
                                           node_id_chec, leader_message, 
                                           node_id_in_message, 
                                           election_id_in_message, node_id >>

check_timeout(self) == start_check_timeout(self) \/ end_check_timeout(self)

start_check_election_message(self) == /\ pc[self] = "start_check_election_message"
                                      /\ IF election_messages[node_id_ch[self]] /= <<>>
                                            THEN /\ election_message' = [election_message EXCEPT ![self] = Head(election_messages[node_id_ch[self]])]
                                                 /\ election_messages' = [election_messages EXCEPT ![node_id_ch[self]] = Tail(election_messages[node_id_ch[self]])]
                                                 /\ node_id_in_message_' = [node_id_in_message_ EXCEPT ![self] = election_message'[self].node_id]
                                                 /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = election_message'[self].connected_count]
                                                 /\ election_id_in_message_' = [election_id_in_message_ EXCEPT ![self] = election_message'[self].election_id]
                                                 /\ IF election_id_in_message_'[self] > election_id[node_id_ch[self]]
                                                       THEN /\ election_id' = [election_id EXCEPT ![node_id_ch[self]] = election_id_in_message_'[self]]
                                                            /\ /\ node_id_' = [node_id_ EXCEPT ![self] = node_id_ch[self]]
                                                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "new_election",
                                                                                                        pc        |->  "end_check_election_message",
                                                                                                        node_id_  |->  node_id_[self] ] >>
                                                                                                    \o stack[self]]
                                                            /\ pc' = [pc EXCEPT ![self] = "start_new_election"]
                                                            /\ UNCHANGED reply_messages
                                                       ELSE /\ IF election_id_in_message_'[self] = election_id[node_id_ch[self]]
                                                                  THEN /\ IF connected_count_in_message'[self] > connected_count[node_id_ch[self]]
                                                                             THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message_'[self]] =                                   Append(reply_messages[node_id_in_message_'[self]],
                                                                                                                                                              [yes |-> TRUE, election_id |-> election_id[node_id_ch[self]]])]
                                                                             ELSE /\ IF connected_count_in_message'[self] = connected_count[node_id_ch[self]]
                                                                                        THEN /\ IF node_id_in_message_'[self] < node_id_ch[self]
                                                                                                   THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message_'[self]] =                                   Append(reply_messages[node_id_in_message_'[self]],
                                                                                                                                                                                    [yes |-> TRUE, election_id |-> election_id[node_id_ch[self]]])]
                                                                                                   ELSE /\ IF node_id_in_message_'[self] = node_id_ch[self]
                                                                                                              THEN /\ UNCHANGED reply_messages
                                                                                                              ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message_'[self]] =                                   Append(reply_messages[node_id_in_message_'[self]],
                                                                                                                                                                                               [yes |-> FALSE, election_id |-> election_id[node_id_ch[self]]])]
                                                                                        ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message_'[self]] =                                   Append(reply_messages[node_id_in_message_'[self]],
                                                                                                                                                                         [yes |-> FALSE, election_id |-> election_id[node_id_ch[self]]])]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED reply_messages
                                                            /\ pc' = [pc EXCEPT ![self] = "end_check_election_message"]
                                                            /\ UNCHANGED << election_id, 
                                                                            stack, 
                                                                            node_id_ >>
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "end_check_election_message"]
                                                 /\ UNCHANGED << election_id, 
                                                                 election_messages, 
                                                                 reply_messages, 
                                                                 stack, 
                                                                 node_id_, 
                                                                 election_message, 
                                                                 node_id_in_message_, 
                                                                 connected_count_in_message, 
                                                                 election_id_in_message_ >>
                                      /\ UNCHANGED << connected_count, 
                                                      yes_count, leader, 
                                                      is_crashed, connected, 
                                                      timeout, state, 
                                                      leader_messages, lock, 
                                                      from_node_, to_node_, 
                                                      message_, from_node, 
                                                      to_node, message, 
                                                      node_id_c, node_id_ch, 
                                                      node_id_che, 
                                                      reply_message, 
                                                      reply_in_massage, 
                                                      election_id_in_message_c, 
                                                      node_id_chec, 
                                                      leader_message, 
                                                      node_id_in_message, 
                                                      election_id_in_message, 
                                                      node_id >>

end_check_election_message(self) == /\ pc[self] = "end_check_election_message"
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ election_message' = [election_message EXCEPT ![self] = Head(stack[self]).election_message]
                                    /\ node_id_in_message_' = [node_id_in_message_ EXCEPT ![self] = Head(stack[self]).node_id_in_message_]
                                    /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = Head(stack[self]).connected_count_in_message]
                                    /\ election_id_in_message_' = [election_id_in_message_ EXCEPT ![self] = Head(stack[self]).election_id_in_message_]
                                    /\ node_id_ch' = [node_id_ch EXCEPT ![self] = Head(stack[self]).node_id_ch]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ UNCHANGED << election_id, 
                                                    connected_count, yes_count, 
                                                    leader, is_crashed, 
                                                    connected, timeout, state, 
                                                    election_messages, 
                                                    reply_messages, 
                                                    leader_messages, lock, 
                                                    from_node_, to_node_, 
                                                    message_, from_node, 
                                                    to_node, message, node_id_, 
                                                    node_id_c, node_id_che, 
                                                    reply_message, 
                                                    reply_in_massage, 
                                                    election_id_in_message_c, 
                                                    node_id_chec, 
                                                    leader_message, 
                                                    node_id_in_message, 
                                                    election_id_in_message, 
                                                    node_id >>

check_election_message(self) == start_check_election_message(self)
                                   \/ end_check_election_message(self)

start_check_reply_message(self) == /\ pc[self] = "start_check_reply_message"
                                   /\ IF reply_messages[node_id_che[self]] /= <<>>
                                         THEN /\ reply_message' = [reply_message EXCEPT ![self] = Head(reply_messages[node_id_che[self]])]
                                              /\ reply_messages' = [reply_messages EXCEPT ![node_id_che[self]] = Tail(reply_messages[node_id_che[self]])]
                                              /\ reply_in_massage' = [reply_in_massage EXCEPT ![self] = reply_message'[self].yes]
                                              /\ election_id_in_message_c' = [election_id_in_message_c EXCEPT ![self] = reply_message'[self].election_id]
                                              /\ IF election_id_in_message_c'[self] = election_id[node_id_che[self]] /\ reply_in_massage'[self]
                                                    THEN /\ yes_count' = [yes_count EXCEPT ![node_id_che[self]] = yes_count[node_id_che[self]] + 1]
                                                         /\ IF yes_count'[node_id_che[self]] = connected_count[node_id_che[self]]
                                                               THEN /\ /\ from_node' = [from_node EXCEPT ![self] = node_id_che[self]]
                                                                       /\ message' = [message EXCEPT ![self] = [node_id |-> node_id_che[self],
                                                                                                               election_id |-> election_id[node_id_che[self]]]]
                                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "send_leader_message_to_all",
                                                                                                                pc        |->  "end_check_reply_message",
                                                                                                                from_node |->  from_node[self],
                                                                                                                to_node   |->  to_node[self],
                                                                                                                message   |->  message[self] ] >>
                                                                                                            \o stack[self]]
                                                                       /\ to_node' = [to_node EXCEPT ![self] = 1]
                                                                    /\ pc' = [pc EXCEPT ![self] = "start_send_leader_message"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "end_check_reply_message"]
                                                                    /\ UNCHANGED << stack, 
                                                                                    from_node, 
                                                                                    to_node, 
                                                                                    message >>
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "end_check_reply_message"]
                                                         /\ UNCHANGED << yes_count, 
                                                                         stack, 
                                                                         from_node, 
                                                                         to_node, 
                                                                         message >>
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "end_check_reply_message"]
                                              /\ UNCHANGED << yes_count, 
                                                              reply_messages, 
                                                              stack, from_node, 
                                                              to_node, message, 
                                                              reply_message, 
                                                              reply_in_massage, 
                                                              election_id_in_message_c >>
                                   /\ UNCHANGED << election_id, 
                                                   connected_count, leader, 
                                                   is_crashed, connected, 
                                                   timeout, state, 
                                                   election_messages, 
                                                   leader_messages, lock, 
                                                   from_node_, to_node_, 
                                                   message_, node_id_, 
                                                   node_id_c, node_id_ch, 
                                                   election_message, 
                                                   node_id_in_message_, 
                                                   connected_count_in_message, 
                                                   election_id_in_message_, 
                                                   node_id_che, node_id_chec, 
                                                   leader_message, 
                                                   node_id_in_message, 
                                                   election_id_in_message, 
                                                   node_id >>

end_check_reply_message(self) == /\ pc[self] = "end_check_reply_message"
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ reply_message' = [reply_message EXCEPT ![self] = Head(stack[self]).reply_message]
                                 /\ reply_in_massage' = [reply_in_massage EXCEPT ![self] = Head(stack[self]).reply_in_massage]
                                 /\ election_id_in_message_c' = [election_id_in_message_c EXCEPT ![self] = Head(stack[self]).election_id_in_message_c]
                                 /\ node_id_che' = [node_id_che EXCEPT ![self] = Head(stack[self]).node_id_che]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << election_id, connected_count, 
                                                 yes_count, leader, is_crashed, 
                                                 connected, timeout, state, 
                                                 election_messages, 
                                                 reply_messages, 
                                                 leader_messages, lock, 
                                                 from_node_, to_node_, 
                                                 message_, from_node, to_node, 
                                                 message, node_id_, node_id_c, 
                                                 node_id_ch, election_message, 
                                                 node_id_in_message_, 
                                                 connected_count_in_message, 
                                                 election_id_in_message_, 
                                                 node_id_chec, leader_message, 
                                                 node_id_in_message, 
                                                 election_id_in_message, 
                                                 node_id >>

check_reply_message(self) == start_check_reply_message(self)
                                \/ end_check_reply_message(self)

start_check_leader_message(self) == /\ pc[self] = "start_check_leader_message"
                                    /\ IF leader_messages[node_id_chec[self]] /= <<>>
                                          THEN /\ leader_message' = [leader_message EXCEPT ![self] = Head(leader_messages[node_id_chec[self]])]
                                               /\ leader_messages' = [leader_messages EXCEPT ![node_id_chec[self]] = Tail(leader_messages[node_id_chec[self]])]
                                               /\ node_id_in_message' = [node_id_in_message EXCEPT ![self] = leader_message'[self].node_id]
                                               /\ election_id_in_message' = [election_id_in_message EXCEPT ![self] = leader_message'[self].election_id]
                                               /\ IF election_id_in_message'[self] = election_id[node_id_chec[self]]
                                                     THEN /\ leader' = [leader EXCEPT ![node_id_chec[self]] = node_id_in_message'[self]]
                                                          /\ state' = [state EXCEPT ![node_id_chec[self]] = 2]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED << leader, 
                                                                          state >>
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << leader, state, 
                                                               leader_messages, 
                                                               leader_message, 
                                                               node_id_in_message, 
                                                               election_id_in_message >>
                                    /\ pc' = [pc EXCEPT ![self] = "end_check_leader_message"]
                                    /\ UNCHANGED << election_id, 
                                                    connected_count, yes_count, 
                                                    is_crashed, connected, 
                                                    timeout, election_messages, 
                                                    reply_messages, lock, 
                                                    stack, from_node_, 
                                                    to_node_, message_, 
                                                    from_node, to_node, 
                                                    message, node_id_, 
                                                    node_id_c, node_id_ch, 
                                                    election_message, 
                                                    node_id_in_message_, 
                                                    connected_count_in_message, 
                                                    election_id_in_message_, 
                                                    node_id_che, reply_message, 
                                                    reply_in_massage, 
                                                    election_id_in_message_c, 
                                                    node_id_chec, node_id >>

end_check_leader_message(self) == /\ pc[self] = "end_check_leader_message"
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ leader_message' = [leader_message EXCEPT ![self] = Head(stack[self]).leader_message]
                                  /\ node_id_in_message' = [node_id_in_message EXCEPT ![self] = Head(stack[self]).node_id_in_message]
                                  /\ election_id_in_message' = [election_id_in_message EXCEPT ![self] = Head(stack[self]).election_id_in_message]
                                  /\ node_id_chec' = [node_id_chec EXCEPT ![self] = Head(stack[self]).node_id_chec]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << election_id, connected_count, 
                                                  yes_count, leader, 
                                                  is_crashed, connected, 
                                                  timeout, state, 
                                                  election_messages, 
                                                  reply_messages, 
                                                  leader_messages, lock, 
                                                  from_node_, to_node_, 
                                                  message_, from_node, to_node, 
                                                  message, node_id_, node_id_c, 
                                                  node_id_ch, election_message, 
                                                  node_id_in_message_, 
                                                  connected_count_in_message, 
                                                  election_id_in_message_, 
                                                  node_id_che, reply_message, 
                                                  reply_in_massage, 
                                                  election_id_in_message_c, 
                                                  node_id >>

check_leader_message(self) == start_check_leader_message(self)
                                 \/ end_check_leader_message(self)

init_run(self) == /\ pc[self] = "init_run"
                  /\ connected' = [connected EXCEPT ![node_id[self]][node_id[self]] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "aquire_lock"]
                  /\ UNCHANGED << election_id, connected_count, yes_count, 
                                  leader, is_crashed, timeout, state, 
                                  election_messages, reply_messages, 
                                  leader_messages, lock, stack, from_node_, 
                                  to_node_, message_, from_node, to_node, 
                                  message, node_id_, node_id_c, node_id_ch, 
                                  election_message, node_id_in_message_, 
                                  connected_count_in_message, 
                                  election_id_in_message_, node_id_che, 
                                  reply_message, reply_in_massage, 
                                  election_id_in_message_c, node_id_chec, 
                                  leader_message, node_id_in_message, 
                                  election_id_in_message, node_id >>

aquire_lock(self) == /\ pc[self] = "aquire_lock"
                     /\ ~lock
                     /\ lock' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "check_crash"]
                     /\ UNCHANGED << election_id, connected_count, yes_count, 
                                     leader, is_crashed, connected, timeout, 
                                     state, election_messages, reply_messages, 
                                     leader_messages, stack, from_node_, 
                                     to_node_, message_, from_node, to_node, 
                                     message, node_id_, node_id_c, node_id_ch, 
                                     election_message, node_id_in_message_, 
                                     connected_count_in_message, 
                                     election_id_in_message_, node_id_che, 
                                     reply_message, reply_in_massage, 
                                     election_id_in_message_c, node_id_chec, 
                                     leader_message, node_id_in_message, 
                                     election_id_in_message, node_id >>

check_crash(self) == /\ pc[self] = "check_crash"
                     /\ IF is_crashed[node_id[self]]
                           THEN /\ lock' = FALSE
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ node_id' = [node_id EXCEPT ![self] = Head(stack[self]).node_id]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "check_finish"]
                                /\ UNCHANGED << lock, stack, node_id >>
                     /\ UNCHANGED << election_id, connected_count, yes_count, 
                                     leader, is_crashed, connected, timeout, 
                                     state, election_messages, reply_messages, 
                                     leader_messages, from_node_, to_node_, 
                                     message_, from_node, to_node, message, 
                                     node_id_, node_id_c, node_id_ch, 
                                     election_message, node_id_in_message_, 
                                     connected_count_in_message, 
                                     election_id_in_message_, node_id_che, 
                                     reply_message, reply_in_massage, 
                                     election_id_in_message_c, node_id_chec, 
                                     leader_message, node_id_in_message, 
                                     election_id_in_message >>

check_finish(self) == /\ pc[self] = "check_finish"
                      /\ IF \A id \in 1..NODE_NUM: (is_crashed[id]
                                                    \/ (state[id] = 2
                                                        /\ election_messages[id] = <<>>
                                                        /\ reply_messages[id] = <<>>
                                                        /\ leader_messages[id] = <<>>))
                            THEN /\ lock' = FALSE
                                 /\ Assert((leader[node_id[self]] = 1), 
                                           "Failure of assertion at line 206, column 13.")
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ node_id' = [node_id EXCEPT ![self] = Head(stack[self]).node_id]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "start_run"]
                                 /\ UNCHANGED << lock, stack, node_id >>
                      /\ UNCHANGED << election_id, connected_count, yes_count, 
                                      leader, is_crashed, connected, timeout, 
                                      state, election_messages, reply_messages, 
                                      leader_messages, from_node_, to_node_, 
                                      message_, from_node, to_node, message, 
                                      node_id_, node_id_c, node_id_ch, 
                                      election_message, node_id_in_message_, 
                                      connected_count_in_message, 
                                      election_id_in_message_, node_id_che, 
                                      reply_message, reply_in_massage, 
                                      election_id_in_message_c, node_id_chec, 
                                      leader_message, node_id_in_message, 
                                      election_id_in_message >>

start_run(self) == /\ pc[self] = "start_run"
                   /\ \/ /\ /\ node_id_c' = [node_id_c EXCEPT ![self] = node_id[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_timeout",
                                                                     pc        |->  "release_lock",
                                                                     node_id_c |->  node_id_c[self] ] >>
                                                                 \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "start_check_timeout"]
                         /\ UNCHANGED <<node_id_ch, election_message, node_id_in_message_, connected_count_in_message, election_id_in_message_, node_id_che, reply_message, reply_in_massage, election_id_in_message_c, node_id_chec, leader_message, node_id_in_message, election_id_in_message>>
                      \/ /\ /\ node_id_ch' = [node_id_ch EXCEPT ![self] = node_id[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_election_message",
                                                                     pc        |->  "release_lock",
                                                                     election_message |->  election_message[self],
                                                                     node_id_in_message_ |->  node_id_in_message_[self],
                                                                     connected_count_in_message |->  connected_count_in_message[self],
                                                                     election_id_in_message_ |->  election_id_in_message_[self],
                                                                     node_id_ch |->  node_id_ch[self] ] >>
                                                                 \o stack[self]]
                         /\ election_message' = [election_message EXCEPT ![self] = defaultInitValue]
                         /\ node_id_in_message_' = [node_id_in_message_ EXCEPT ![self] = defaultInitValue]
                         /\ connected_count_in_message' = [connected_count_in_message EXCEPT ![self] = defaultInitValue]
                         /\ election_id_in_message_' = [election_id_in_message_ EXCEPT ![self] = defaultInitValue]
                         /\ pc' = [pc EXCEPT ![self] = "start_check_election_message"]
                         /\ UNCHANGED <<node_id_c, node_id_che, reply_message, reply_in_massage, election_id_in_message_c, node_id_chec, leader_message, node_id_in_message, election_id_in_message>>
                      \/ /\ /\ node_id_che' = [node_id_che EXCEPT ![self] = node_id[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_reply_message",
                                                                     pc        |->  "release_lock",
                                                                     reply_message |->  reply_message[self],
                                                                     reply_in_massage |->  reply_in_massage[self],
                                                                     election_id_in_message_c |->  election_id_in_message_c[self],
                                                                     node_id_che |->  node_id_che[self] ] >>
                                                                 \o stack[self]]
                         /\ reply_message' = [reply_message EXCEPT ![self] = defaultInitValue]
                         /\ reply_in_massage' = [reply_in_massage EXCEPT ![self] = defaultInitValue]
                         /\ election_id_in_message_c' = [election_id_in_message_c EXCEPT ![self] = defaultInitValue]
                         /\ pc' = [pc EXCEPT ![self] = "start_check_reply_message"]
                         /\ UNCHANGED <<node_id_c, node_id_ch, election_message, node_id_in_message_, connected_count_in_message, election_id_in_message_, node_id_chec, leader_message, node_id_in_message, election_id_in_message>>
                      \/ /\ /\ node_id_chec' = [node_id_chec EXCEPT ![self] = node_id[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "check_leader_message",
                                                                     pc        |->  "release_lock",
                                                                     leader_message |->  leader_message[self],
                                                                     node_id_in_message |->  node_id_in_message[self],
                                                                     election_id_in_message |->  election_id_in_message[self],
                                                                     node_id_chec |->  node_id_chec[self] ] >>
                                                                 \o stack[self]]
                         /\ leader_message' = [leader_message EXCEPT ![self] = defaultInitValue]
                         /\ node_id_in_message' = [node_id_in_message EXCEPT ![self] = defaultInitValue]
                         /\ election_id_in_message' = [election_id_in_message EXCEPT ![self] = defaultInitValue]
                         /\ pc' = [pc EXCEPT ![self] = "start_check_leader_message"]
                         /\ UNCHANGED <<node_id_c, node_id_ch, election_message, node_id_in_message_, connected_count_in_message, election_id_in_message_, node_id_che, reply_message, reply_in_massage, election_id_in_message_c>>
                   /\ UNCHANGED << election_id, connected_count, yes_count, 
                                   leader, is_crashed, connected, timeout, 
                                   state, election_messages, reply_messages, 
                                   leader_messages, lock, from_node_, to_node_, 
                                   message_, from_node, to_node, message, 
                                   node_id_, node_id >>

release_lock(self) == /\ pc[self] = "release_lock"
                      /\ lock' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "aquire_lock"]
                      /\ UNCHANGED << election_id, connected_count, yes_count, 
                                      leader, is_crashed, connected, timeout, 
                                      state, election_messages, reply_messages, 
                                      leader_messages, stack, from_node_, 
                                      to_node_, message_, from_node, to_node, 
                                      message, node_id_, node_id_c, node_id_ch, 
                                      election_message, node_id_in_message_, 
                                      connected_count_in_message, 
                                      election_id_in_message_, node_id_che, 
                                      reply_message, reply_in_massage, 
                                      election_id_in_message_c, node_id_chec, 
                                      leader_message, node_id_in_message, 
                                      election_id_in_message, node_id >>

run(self) == init_run(self) \/ aquire_lock(self) \/ check_crash(self)
                \/ check_finish(self) \/ start_run(self)
                \/ release_lock(self)

start_process(self) == /\ pc[self] = "start_process"
                       /\ IF self = NODE_NUM+1
                             THEN /\ is_crashed' = [is_crashed EXCEPT ![1] = TRUE]
                                  /\ timeout' = <<FALSE, TRUE, TRUE, TRUE>>
                                  /\ connected' =              <<
                                                      <<FALSE, FALSE, FALSE, FALSE>>,
                                                      <<FALSE, FALSE, TRUE,  TRUE>>,
                                                      <<FALSE, TRUE,  FALSE, TRUE>>,
                                                      <<FALSE, TRUE,  TRUE,  FALSE>>
                                                  >>
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, node_id >>
                             ELSE /\ /\ node_id' = [node_id EXCEPT ![self] = self]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run",
                                                                              pc        |->  "Done",
                                                                              node_id   |->  node_id[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "init_run"]
                                  /\ UNCHANGED << is_crashed, connected, 
                                                  timeout >>
                       /\ UNCHANGED << election_id, connected_count, yes_count, 
                                       leader, state, election_messages, 
                                       reply_messages, leader_messages, lock, 
                                       from_node_, to_node_, message_, 
                                       from_node, to_node, message, node_id_, 
                                       node_id_c, node_id_ch, election_message, 
                                       node_id_in_message_, 
                                       connected_count_in_message, 
                                       election_id_in_message_, node_id_che, 
                                       reply_message, reply_in_massage, 
                                       election_id_in_message_c, node_id_chec, 
                                       leader_message, node_id_in_message, 
                                       election_id_in_message >>

N(self) == start_process(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ send_election_message_to_all(self)
                               \/ send_leader_message_to_all(self)
                               \/ new_election(self) \/ check_timeout(self)
                               \/ check_election_message(self)
                               \/ check_reply_message(self)
                               \/ check_leader_message(self) \/ run(self))
           \/ (\E self \in 1..NODE_NUM+1: N(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NODE_NUM+1 : /\ SF_vars(N(self))
                                       /\ SF_vars(run(self))
                                       /\ SF_vars(send_election_message_to_all(self))                                       /\ SF_vars(send_leader_message_to_all(self))                                       /\ SF_vars(new_election(self))
                                       /\ SF_vars(check_timeout(self))
                                       /\ SF_vars(check_election_message(self))                                       /\ SF_vars(check_reply_message(self))
                                       /\ SF_vars(check_leader_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
