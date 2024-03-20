----------------- MODULE leader_election ----------------
EXTENDS TLC, Integers, Sequences

(*--algorithm leader_election

variables
    term = [x \in 1..4 |-> 0];
    connected_count = [x \in 1..4 |->3];
    yes_count = [x \in 1..4 |-> 0];
    leader = [x \in 1..4 |-> 0];
    is_crashed = [x \in 1..4 |-> FALSE];
    connected = [x \in 1..4 |-> [y \in 1..4 |-> TRUE]];
    timeout = [x \in 1..4 |-> FALSE];

    \* queues
    election_messages = [x \in 1..4 |-> <<>>];
    reply_messages = [x \in 1..4 |-> <<>>];
    leader_messages = [x \in 1..4 |-> <<>>];

    start = FALSE;
    expected_leader = 0;

    msg1;
    msg2;
    msg3;
    msg4;

    message;
    reply_message;
    reply_in_massage;
    leader_message;
    node_id_in_message;
    term_in_message;
    election_message,
    connected_count_in_message,

macro set_msg1(from, messages, message, default) begin
    if connected[from][1] then
        msg1 := Append(messages[1], message);
    elsif from = 1 then
        msg1 := default;
    else
        msg1 := messages[1];
    end if;
end macro;

macro set_msg2(from, messages, message, default) begin
    if connected[from][2] then
        msg2 := Append(messages[2], message);
    elsif from = 2 then
        msg2 := default;
    else
        msg2 := messages[2];
    end if;
end macro;

macro set_msg3(from, messages, message, default) begin
    if connected[from][3] then
        msg3 := Append(messages[3], message);
    elsif from = 3 then
        msg3 := default;
    else
        msg3 := messages[3];
    end if;
end macro;

macro set_msg4(from, messages, message, default) begin
    if connected[from][4] then
        msg4 := Append(messages[4], message);
    elsif from = 4 then
        msg4 := default;
    else
        msg4 := messages[4];
    end if;
end macro;

\* function for sending election messages to all nodes
macro send_election_message_to_all(node_id, message) begin
    set_msg1(node_id, election_messages, message, election_messages[1]);
    set_msg2(node_id, election_messages, message, election_messages[2]);
    set_msg3(node_id, election_messages, message, election_messages[3]);
    set_msg4(node_id, election_messages, message, election_messages[4]);
    election_messages := <<msg1, msg2, msg3, msg4>>;
end macro;

\* function for sending leader messages to all nodes
macro send_leader_message_to_all(node_id, message) begin
    set_msg1(node_id, leader_messages, message, leader_messages[1]);
    set_msg2(node_id, leader_messages, message, leader_messages[2]);
    set_msg3(node_id, leader_messages, message, leader_messages[3]);
    set_msg4(node_id, leader_messages, message, leader_messages[4]);
    leader_messages := <<msg1, msg2, msg3, msg4>>;
end macro;

\* function for checking reply messages
macro check_reply_message(node_id) begin
    reply_message := Head(reply_messages[node_id]);
    reply_messages[node_id] := Tail(reply_messages[node_id]);
    reply_in_massage := reply_message.yes;
    term_in_message := reply_message.term;

    \* if term is the same and the reply is YES, increment YES count
    if term_in_message = term[node_id] /\ reply_in_massage then
        yes_count[node_id] := yes_count[node_id] + 1;

        \* if YES count increses to connected_count, send leader message to all nodes
        if yes_count[node_id] = connected_count[node_id] then
            leader[node_id] := node_id;
            send_leader_message_to_all(node_id,
                [node_id |-> node_id,
                term |-> term[node_id]])
        end if;
    end if;
end macro;

\* function for checking leader messages
macro check_leader_message(node_id) begin
    leader_message := Head(leader_messages[node_id]);
    leader_messages[node_id] := Tail(leader_messages[node_id]);
    node_id_in_message := leader_message.node_id;
    term_in_message := leader_message.term;

    \* if term is the same, update the leader
    if term_in_message = term[node_id] then
        leader[node_id] := node_id_in_message;
    end if;
end macro;

\* function for checking timeout
macro check_timeout(node_id) begin
    timeout[node_id] := FALSE;
    connected_count[node_id] := connected_count[node_id] - 1;
    term[node_id] := term[node_id] + 1;
        
    yes_count[node_id] := 0;
    send_election_message_to_all(node_id,
        [node_id |-> node_id,
        connected_count |-> connected_count[node_id],
        term |-> term[node_id]]);
end macro;

\* function for checking election messages
macro check_election_message(node_id) begin
    election_message := Head(election_messages[node_id]);
    node_id_in_message := election_message.node_id;
    connected_count_in_message := election_message.connected_count;
    term_in_message := election_message.term;

    \* if term in msg is bigger than mine, start new election and reply
    if term_in_message > term[node_id] then
        term[node_id] := term_in_message;
        yes_count[node_id] := 0;
        message := [node_id |-> node_id,
            connected_count |-> connected_count[node_id],
            term |-> term[node_id]];
        set_msg1(node_id, election_messages, message, Tail(election_messages[node_id]));
        set_msg2(node_id, election_messages, message, Tail(election_messages[node_id]));
        set_msg3(node_id, election_messages, message, Tail(election_messages[node_id]));
        set_msg4(node_id, election_messages, message, Tail(election_messages[node_id]));
        election_messages := <<msg1, msg2, msg3, msg4>>;
    else
        election_messages[node_id] := Tail(election_messages[node_id]);
    end if;

    \* if term in msg is bigger or the same as mine, send reply message
    if term_in_message = term[node_id] then
        if connected_count_in_message > connected_count[node_id] then
            \* reply Yes
            reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                [yes |-> TRUE, term |-> term[node_id]]);
        elsif connected_count_in_message = connected_count[node_id] then
            if node_id_in_message < node_id then
                \* reply Yes
                reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                    [yes |-> TRUE, term |-> term[node_id]]);
            elsif node_id_in_message = node_id then
                \* do nothing. it's my own message
            else
                \* reply No
                reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                    [yes |-> FALSE, term |-> term[node_id]]);
            end if;
        else
            \* reply No
            reply_messages[node_id_in_message] := Append(reply_messages[node_id_in_message],
                [yes |-> FALSE, term |-> term[node_id]]);
        end if;
    else
        \* do nothing
    end if;
end macro;

procedure run(node_id) begin
    \* represent non-deterministic execution
    loop:
        either
            await timeout[node_id];
            check_timeout(node_id);
        or
            await election_messages[node_id] /= <<>>;
            check_election_message(node_id);
        or
            await reply_messages[node_id] /= <<>>;
            check_reply_message(node_id);
        or
            await leader_messages[node_id] /= <<>>;
            check_leader_message(node_id);
        or
            await \A id \in 1..4: (
                is_crashed[id]
                \/ (timeout[id] = FALSE
                    /\ election_messages[id] = <<>>
                    /\ reply_messages[id] = <<>>
                    /\ leader_messages[id] = <<>>));

            assert(leader[node_id] = expected_leader);
            return;
        end either;

    jump:
        goto loop;
end procedure;

\* Process 1..4 represent the nodes.
\* Process 5 represents dummy process which invoke node or link crashes.
\* Please initialize is_crashed, timeout, expected_leader and connected variables manually.
fair process N \in 1..4
begin
    start_process:
        if self = 1 then
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

            start := TRUE;
        end if;
        
        await start;
        if ~is_crashed[self] then
            call run(self);
        end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cd1aa0ab" /\ chksum(tla) = "e2a0362b")
CONSTANT defaultInitValue
VARIABLES term, connected_count, yes_count, leader, is_crashed, 
          connected, timeout, election_messages, reply_messages, 
          leader_messages, start, expected_leader, msg1, msg2, msg3, msg4, 
          message, reply_message, reply_in_massage, leader_message, 
          node_id_in_message, term_in_message, election_message, 
          connected_count_in_message, pc, stack, node_id

vars == << term, connected_count, yes_count, leader, is_crashed, 
           connected, timeout, election_messages, reply_messages, 
           leader_messages, start, expected_leader, msg1, msg2, msg3, msg4, 
           message, reply_message, reply_in_massage, leader_message, 
           node_id_in_message, term_in_message, election_message, 
           connected_count_in_message, pc, stack, node_id >>

ProcSet == (1..4)

Init == (* Global variables *)
        /\ term = [x \in 1..4 |-> 0]
        /\ connected_count = [x \in 1..4 |->3]
        /\ yes_count = [x \in 1..4 |-> 0]
        /\ leader = [x \in 1..4 |-> 0]
        /\ is_crashed = [x \in 1..4 |-> FALSE]
        /\ connected = [x \in 1..4 |-> [y \in 1..4 |-> TRUE]]
        /\ timeout = [x \in 1..4 |-> FALSE]
        /\ election_messages = [x \in 1..4 |-> <<>>]
        /\ reply_messages = [x \in 1..4 |-> <<>>]
        /\ leader_messages = [x \in 1..4 |-> <<>>]
        /\ start = FALSE
        /\ expected_leader = 0
        /\ msg1 = defaultInitValue
        /\ msg2 = defaultInitValue
        /\ msg3 = defaultInitValue
        /\ msg4 = defaultInitValue
        /\ message = defaultInitValue
        /\ reply_message = defaultInitValue
        /\ reply_in_massage = defaultInitValue
        /\ leader_message = defaultInitValue
        /\ node_id_in_message = defaultInitValue
        /\ term_in_message = defaultInitValue
        /\ election_message = defaultInitValue
        /\ connected_count_in_message = defaultInitValue
        (* Procedure run *)
        /\ node_id = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_process"]

loop(self) == /\ pc[self] = "loop"
              /\ \/ /\ timeout[node_id[self]]
                    /\ timeout' = [timeout EXCEPT ![node_id[self]] = FALSE]
                    /\ connected_count' = [connected_count EXCEPT ![node_id[self]] = connected_count[node_id[self]] - 1]
                    /\ term' = [term EXCEPT ![node_id[self]] = term[node_id[self]] + 1]
                    /\ yes_count' = [yes_count EXCEPT ![node_id[self]] = 0]
                    /\ IF connected[node_id[self]][1]
                          THEN /\ msg1' = Append(election_messages[1], ([node_id |-> node_id[self],
                                                                        connected_count |-> connected_count'[node_id[self]],
                                                                        term |-> term'[node_id[self]]]))
                          ELSE /\ IF node_id[self] = 1
                                     THEN /\ msg1' = election_messages[1]
                                     ELSE /\ msg1' = election_messages[1]
                    /\ IF connected[node_id[self]][2]
                          THEN /\ msg2' = Append(election_messages[2], ([node_id |-> node_id[self],
                                                                        connected_count |-> connected_count'[node_id[self]],
                                                                        term |-> term'[node_id[self]]]))
                          ELSE /\ IF node_id[self] = 2
                                     THEN /\ msg2' = election_messages[2]
                                     ELSE /\ msg2' = election_messages[2]
                    /\ IF connected[node_id[self]][3]
                          THEN /\ msg3' = Append(election_messages[3], ([node_id |-> node_id[self],
                                                                        connected_count |-> connected_count'[node_id[self]],
                                                                        term |-> term'[node_id[self]]]))
                          ELSE /\ IF node_id[self] = 3
                                     THEN /\ msg3' = election_messages[3]
                                     ELSE /\ msg3' = election_messages[3]
                    /\ IF connected[node_id[self]][4]
                          THEN /\ msg4' = Append(election_messages[4], ([node_id |-> node_id[self],
                                                                        connected_count |-> connected_count'[node_id[self]],
                                                                        term |-> term'[node_id[self]]]))
                          ELSE /\ IF node_id[self] = 4
                                     THEN /\ msg4' = election_messages[4]
                                     ELSE /\ msg4' = election_messages[4]
                    /\ election_messages' = <<msg1', msg2', msg3', msg4'>>
                    /\ pc' = [pc EXCEPT ![self] = "jump"]
                    /\ UNCHANGED <<leader, reply_messages, leader_messages, message, reply_message, reply_in_massage, leader_message, node_id_in_message, term_in_message, election_message, connected_count_in_message, stack, node_id>>
                 \/ /\ election_messages[node_id[self]] /= <<>>
                    /\ election_message' = Head(election_messages[node_id[self]])
                    /\ node_id_in_message' = election_message'.node_id
                    /\ connected_count_in_message' = election_message'.connected_count
                    /\ term_in_message' = election_message'.term
                    /\ IF term_in_message' > term[node_id[self]]
                          THEN /\ term' = [term EXCEPT ![node_id[self]] = term_in_message']
                               /\ yes_count' = [yes_count EXCEPT ![node_id[self]] = 0]
                               /\ message' =        [node_id |-> node_id[self],
                                             connected_count |-> connected_count[node_id[self]],
                                             term |-> term'[node_id[self]]]
                               /\ IF connected[node_id[self]][1]
                                     THEN /\ msg1' = Append(election_messages[1], message')
                                     ELSE /\ IF node_id[self] = 1
                                                THEN /\ msg1' = Tail(election_messages[node_id[self]])
                                                ELSE /\ msg1' = election_messages[1]
                               /\ IF connected[node_id[self]][2]
                                     THEN /\ msg2' = Append(election_messages[2], message')
                                     ELSE /\ IF node_id[self] = 2
                                                THEN /\ msg2' = Tail(election_messages[node_id[self]])
                                                ELSE /\ msg2' = election_messages[2]
                               /\ IF connected[node_id[self]][3]
                                     THEN /\ msg3' = Append(election_messages[3], message')
                                     ELSE /\ IF node_id[self] = 3
                                                THEN /\ msg3' = Tail(election_messages[node_id[self]])
                                                ELSE /\ msg3' = election_messages[3]
                               /\ IF connected[node_id[self]][4]
                                     THEN /\ msg4' = Append(election_messages[4], message')
                                     ELSE /\ IF node_id[self] = 4
                                                THEN /\ msg4' = Tail(election_messages[node_id[self]])
                                                ELSE /\ msg4' = election_messages[4]
                               /\ election_messages' = <<msg1', msg2', msg3', msg4'>>
                          ELSE /\ election_messages' = [election_messages EXCEPT ![node_id[self]] = Tail(election_messages[node_id[self]])]
                               /\ UNCHANGED << term, yes_count, msg1, 
                                               msg2, msg3, msg4, message >>
                    /\ IF term_in_message' = term'[node_id[self]]
                          THEN /\ IF connected_count_in_message' > connected_count[node_id[self]]
                                     THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                               [yes |-> TRUE, term |-> term'[node_id[self]]])]
                                     ELSE /\ IF connected_count_in_message' = connected_count[node_id[self]]
                                                THEN /\ IF node_id_in_message' < node_id[self]
                                                           THEN /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                     [yes |-> TRUE, term |-> term'[node_id[self]]])]
                                                           ELSE /\ IF node_id_in_message' = node_id[self]
                                                                      THEN /\ UNCHANGED reply_messages
                                                                      ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                                                [yes |-> FALSE, term |-> term'[node_id[self]]])]
                                                ELSE /\ reply_messages' = [reply_messages EXCEPT ![node_id_in_message'] =                                   Append(reply_messages[node_id_in_message'],
                                                                                                                          [yes |-> FALSE, term |-> term'[node_id[self]]])]
                          ELSE /\ TRUE
                               /\ UNCHANGED reply_messages
                    /\ pc' = [pc EXCEPT ![self] = "jump"]
                    /\ UNCHANGED <<connected_count, leader, timeout, leader_messages, reply_message, reply_in_massage, leader_message, stack, node_id>>
                 \/ /\ reply_messages[node_id[self]] /= <<>>
                    /\ reply_message' = Head(reply_messages[node_id[self]])
                    /\ reply_messages' = [reply_messages EXCEPT ![node_id[self]] = Tail(reply_messages[node_id[self]])]
                    /\ reply_in_massage' = reply_message'.yes
                    /\ term_in_message' = reply_message'.term
                    /\ IF term_in_message' = term[node_id[self]] /\ reply_in_massage'
                          THEN /\ yes_count' = [yes_count EXCEPT ![node_id[self]] = yes_count[node_id[self]] + 1]
                               /\ IF yes_count'[node_id[self]] = connected_count[node_id[self]]
                                     THEN /\ leader' = [leader EXCEPT ![node_id[self]] = node_id[self]]
                                          /\ IF connected[node_id[self]][1]
                                                THEN /\ msg1' = Append(leader_messages[1], ([node_id |-> node_id[self],
                                                                                            term |-> term[node_id[self]]]))
                                                ELSE /\ IF node_id[self] = 1
                                                           THEN /\ msg1' = leader_messages[1]
                                                           ELSE /\ msg1' = leader_messages[1]
                                          /\ IF connected[node_id[self]][2]
                                                THEN /\ msg2' = Append(leader_messages[2], ([node_id |-> node_id[self],
                                                                                            term |-> term[node_id[self]]]))
                                                ELSE /\ IF node_id[self] = 2
                                                           THEN /\ msg2' = leader_messages[2]
                                                           ELSE /\ msg2' = leader_messages[2]
                                          /\ IF connected[node_id[self]][3]
                                                THEN /\ msg3' = Append(leader_messages[3], ([node_id |-> node_id[self],
                                                                                            term |-> term[node_id[self]]]))
                                                ELSE /\ IF node_id[self] = 3
                                                           THEN /\ msg3' = leader_messages[3]
                                                           ELSE /\ msg3' = leader_messages[3]
                                          /\ IF connected[node_id[self]][4]
                                                THEN /\ msg4' = Append(leader_messages[4], ([node_id |-> node_id[self],
                                                                                            term |-> term[node_id[self]]]))
                                                ELSE /\ IF node_id[self] = 4
                                                           THEN /\ msg4' = leader_messages[4]
                                                           ELSE /\ msg4' = leader_messages[4]
                                          /\ leader_messages' = <<msg1', msg2', msg3', msg4'>>
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << leader, 
                                                          leader_messages, 
                                                          msg1, msg2, msg3, 
                                                          msg4 >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << yes_count, leader, 
                                               leader_messages, msg1, msg2, 
                                               msg3, msg4 >>
                    /\ pc' = [pc EXCEPT ![self] = "jump"]
                    /\ UNCHANGED <<term, connected_count, timeout, election_messages, message, leader_message, node_id_in_message, election_message, connected_count_in_message, stack, node_id>>
                 \/ /\ leader_messages[node_id[self]] /= <<>>
                    /\ leader_message' = Head(leader_messages[node_id[self]])
                    /\ leader_messages' = [leader_messages EXCEPT ![node_id[self]] = Tail(leader_messages[node_id[self]])]
                    /\ node_id_in_message' = leader_message'.node_id
                    /\ term_in_message' = leader_message'.term
                    /\ IF term_in_message' = term[node_id[self]]
                          THEN /\ leader' = [leader EXCEPT ![node_id[self]] = node_id_in_message']
                          ELSE /\ TRUE
                               /\ UNCHANGED leader
                    /\ pc' = [pc EXCEPT ![self] = "jump"]
                    /\ UNCHANGED <<term, connected_count, yes_count, timeout, election_messages, reply_messages, msg1, msg2, msg3, msg4, message, reply_message, reply_in_massage, election_message, connected_count_in_message, stack, node_id>>
                 \/ /\   \A id \in 1..4: (
                       is_crashed[id]
                       \/ (timeout[id] = FALSE
                           /\ election_messages[id] = <<>>
                           /\ reply_messages[id] = <<>>
                           /\ leader_messages[id] = <<>>))
                    /\ Assert((leader[node_id[self]] = expected_leader), 
                              "Failure of assertion at line 216, column 13.")
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ node_id' = [node_id EXCEPT ![self] = Head(stack[self]).node_id]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED <<term, connected_count, yes_count, leader, timeout, election_messages, reply_messages, leader_messages, msg1, msg2, msg3, msg4, message, reply_message, reply_in_massage, leader_message, node_id_in_message, term_in_message, election_message, connected_count_in_message>>
              /\ UNCHANGED << is_crashed, connected, start, expected_leader >>

jump(self) == /\ pc[self] = "jump"
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << term, connected_count, yes_count, leader, 
                              is_crashed, connected, timeout, 
                              election_messages, reply_messages, 
                              leader_messages, start, expected_leader, msg1, 
                              msg2, msg3, msg4, message, reply_message, 
                              reply_in_massage, leader_message, 
                              node_id_in_message, term_in_message, 
                              election_message, connected_count_in_message, 
                              stack, node_id >>

run(self) == loop(self) \/ jump(self)

start_process(self) == /\ pc[self] = "start_process"
                       /\ IF self = 1
                             THEN /\ is_crashed' = [is_crashed EXCEPT ![1] = TRUE]
                                  /\ timeout' = <<FALSE, TRUE, TRUE, TRUE>>
                                  /\ expected_leader' = 2
                                  /\ connected' =              <<
                                                      <<FALSE, FALSE, FALSE, FALSE>>,
                                                      <<FALSE, FALSE, TRUE, TRUE>>,
                                                      <<FALSE, TRUE, FALSE, TRUE>>,
                                                      <<FALSE, TRUE, TRUE, FALSE>>
                                                  >>
                                  /\ start' = TRUE
                             ELSE /\ TRUE
                                  /\ UNCHANGED << is_crashed, connected, 
                                                  timeout, start, 
                                                  expected_leader >>
                       /\ start'
                       /\ IF ~is_crashed'[self]
                             THEN /\ /\ node_id' = [node_id EXCEPT ![self] = self]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run",
                                                                              pc        |->  "Done",
                                                                              node_id   |->  node_id[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "loop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, node_id >>
                       /\ UNCHANGED << term, connected_count, yes_count, 
                                       leader, election_messages, 
                                       reply_messages, leader_messages, msg1, 
                                       msg2, msg3, msg4, message, 
                                       reply_message, reply_in_massage, 
                                       leader_message, node_id_in_message, 
                                       term_in_message, 
                                       election_message, 
                                       connected_count_in_message >>

N(self) == start_process(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: run(self))
           \/ (\E self \in 1..4: N(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..4 : WF_vars(N(self)) /\ WF_vars(run(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
