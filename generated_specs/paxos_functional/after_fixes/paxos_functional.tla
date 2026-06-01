---- MODULE paxos_functional ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,          \* Set of all nodes in the system (expected to be integers for tie-breaking)
    Values,         \* Set of consensus values that can be proposed
    InitialLeader   \* The initial leader node (can be None)

None == "None"

NilProposal == [number |-> 0, uid |-> CHOOSE n \in Nodes : TRUE]

VARIABLES 
    msgs,                  \* Set of all messages in flight
    proposal_id,           \* Current proposal ID of each node
    next_proposal_number,  \* Counter for proposal numbers
    promises_rcvd,         \* Sets of promises received per node
    leader,                \* Boolean flag per node indicating leadership
    promised_id,           \* Highest promised proposal ID per node
    accepted_id,           \* Highest accepted proposal ID per node
    accepted_value,        \* Last accepted value per node
    pending_promise,       \* Staged node for pending promise message (or None)
    pending_accepted,      \* Staged node for pending accepted message (or None)
    final_value,           \* Consensus resolved value (or None)
    final_proposal_id,     \* Proposal ID of resolved consensus value (or NilProposal)
    final_acceptors,       \* Set of acceptors that accepted final value
    leader_uid,            \* Belief of current leader UID (or None)
    _nacks,                \* Set of nodes that rejected the current proposal
    proposed_value,        \* Value proposed by this node (or None)
    leader_proposal_id,    \* Active leader proposal ID (or NilProposal)
    _acquiring,            \* Boolean indicating leadership acquisition
    active_votes,          \* Set of learner votes per node
    last_accepted_id,      \* Proposer tracking of highest accepted ID
    leader_alive           \* Belief about leader liveness

vars == <<msgs, proposal_id, next_proposal_number, promises_rcvd, leader, promised_id, 
          accepted_id, accepted_value, pending_promise, pending_accepted, final_value, 
          final_proposal_id, final_acceptors, leader_uid, _nacks, proposed_value, 
          leader_proposal_id, _acquiring, active_votes, last_accepted_id, leader_alive>>

GreaterThan(p1, p2) ==
    \/ p1.number > p2.number
    \/ (p1.number = p2.number /\ p1.uid > p2.uid)

LessThan(p1, p2) ==
    \/ p1.number < p2.number
    \/ (p1.number = p2.number /\ p1.uid < p2.uid)

GreaterOrEqual(p1, p2) ==
    \/ GreaterThan(p1, p2)
    \/ p1 = p2

LessOrEqual(p1, p2) ==
    \/ LessThan(p1, p2)
    \/ p1 = p2

ObserveProposal(node, from_uid, pid) ==
    IF from_uid /= node /\ GreaterOrEqual(pid, [number |-> next_proposal_number[node], uid |-> node])
    THEN pid.number + 1
    ELSE next_proposal_number[node]

QuorumSize == (Cardinality(Nodes) \div 2) + 1

Init ==
    /\ msgs = {}
    /\ proposal_id = [n \in Nodes |-> IF n = InitialLeader THEN [number |-> 1, uid |-> n] ELSE NilProposal]
    /\ next_proposal_number = [n \in Nodes |-> IF n = InitialLeader THEN 2 ELSE 1]
    /\ promises_rcvd = [n \in Nodes |-> {}]
    /\ leader = [n \in Nodes |-> IF n = InitialLeader THEN TRUE ELSE FALSE]
    /\ promised_id = [n \in Nodes |-> NilProposal]
    /\ accepted_id = [n \in Nodes |-> NilProposal]
    /\ accepted_value = [n \in Nodes |-> None]
    /\ pending_promise = [n \in Nodes |-> None]
    /\ pending_accepted = [n \in Nodes |-> None]
    /\ final_value = [n \in Nodes |-> None]
    /\ final_proposal_id = [n \in Nodes |-> NilProposal]
    /\ final_acceptors = [n \in Nodes |-> {}]
    /\ leader_uid = [n \in Nodes |-> IF InitialLeader /= None THEN InitialLeader ELSE None]
    /\ _nacks = [n \in Nodes |-> {}]
    /\ proposed_value = [n \in Nodes |-> None]
    /\ leader_proposal_id = [n \in Nodes |-> IF InitialLeader /= None THEN [number |-> 1, uid |-> InitialLeader] ELSE NilProposal]
    /\ _acquiring = [n \in Nodes |-> FALSE]
    /\ active_votes = [n \in Nodes |-> {}]
    /\ last_accepted_id = [n \in Nodes |-> NilProposal]
    /\ leader_alive = [n \in Nodes |-> TRUE]

SetProposal(node, val) ==
    /\ proposed_value[node] = None
    /\ proposed_value' = [proposed_value EXCEPT ![node] = val]
    /\ IF leader[node]
       THEN msgs' = msgs \cup {[type |-> "Accept", proposal_id |-> proposal_id[node], value |-> val, from |-> node]}
       ELSE UNCHANGED msgs
    /\ UNCHANGED <<proposal_id, next_proposal_number, promises_rcvd, leader, promised_id, 
                  accepted_id, accepted_value, pending_promise, pending_accepted, final_value, 
                  final_proposal_id, final_acceptors, leader_uid, _nacks, leader_proposal_id, 
                  _acquiring, active_votes, last_accepted_id, leader_alive>>

PollLiveness(node) ==
    /\ leader_alive[node] = FALSE
    /\ _acquiring' = [_acquiring EXCEPT ![node] = TRUE]
    /\ leader' = [leader EXCEPT ![node] = FALSE]
    /\ promises_rcvd' = [promises_rcvd EXCEPT ![node] = {}]
    /\ proposal_id' = [proposal_id EXCEPT ![node] = [number |-> next_proposal_number[node], uid |-> node]]
    /\ next_proposal_number' = [next_proposal_number EXCEPT ![node] = next_proposal_number[node] + 1]
    /\ _nacks' = [_nacks EXCEPT ![node] = {}]
    /\ msgs' = msgs \cup {[type |-> "Prepare", proposal_id |-> [number |-> next_proposal_number[node], uid |-> node], from |-> node]}
    /\ UNCHANGED <<promised_id, accepted_id, accepted_value, pending_promise, pending_accepted, final_value, 
                  final_proposal_id, final_acceptors, leader_uid, proposed_value, leader_proposal_id, 
                  active_votes, last_accepted_id, leader_alive>>

Timeout(node) ==
    /\ leader_alive[node] = TRUE
    /\ leader_alive' = [leader_alive EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<msgs, proposal_id, next_proposal_number, promises_rcvd, leader, promised_id, 
                  accepted_id, accepted_value, pending_promise, pending_accepted, final_value, 
                  final_proposal_id, final_acceptors, leader_uid, _nacks, proposed_value, 
                  leader_proposal_id, _acquiring, active_votes, last_accepted_id>>

Persisted(node) ==
    /\ \/ pending_promise[node] /= None
       \/ pending_accepted[node] /= None
    /\ LET promise_msg == IF pending_promise[node] /= None
                          THEN {[type |-> "Promise", to |-> pending_promise[node], from |-> node, 
                                 proposal_id |-> promised_id[node], prev_accepted_id |-> accepted_id[node], 
                                 prev_accepted_value |-> accepted_value[node]]}
                          ELSE {}
           accepted_msg == IF pending_accepted[node] /= None
                           THEN {[type |-> "Accepted", proposal_id |-> accepted_id[node], 
                                  value |-> accepted_value[node], from |-> node]}
                           ELSE {}
       IN
         /\ msgs' = msgs \cup promise_msg \cup accepted_msg
         /\ pending_promise' = [pending_promise EXCEPT ![node] = None]
         /\ pending_accepted' = [pending_accepted EXCEPT ![node] = None]
    /\ UNCHANGED <<proposal_id, next_proposal_number, promises_rcvd, leader, promised_id, 
                  accepted_id, accepted_value, final_value, final_proposal_id, final_acceptors, 
                  leader_uid, _nacks, proposed_value, leader_proposal_id, _acquiring, 
                  active_votes, last_accepted_id, leader_alive>>

RecvPrepare(node, msg) ==
    /\ msg.type = "Prepare"
    /\ msg.from \in Nodes
    /\ IF msg.proposal_id = promised_id[node]
       THEN 
         /\ msgs' = msgs \cup {[type |-> "Promise", to |-> msg.from, from |-> node, 
                                proposal_id |-> msg.proposal_id, prev_accepted_id |-> accepted_id[node], 
                                prev_accepted_value |-> accepted_value[node]]}
         /\ UNCHANGED <<promised_id, pending_promise>>
       ELSE IF GreaterThan(msg.proposal_id, promised_id[node])
       THEN
         IF pending_promise[node] = None
         THEN 
           /\ promised_id' = [promised_id EXCEPT ![node] = msg.proposal_id]
           /\ pending_promise' = [pending_promise EXCEPT ![node] = msg.from]
           /\ UNCHANGED msgs
         ELSE UNCHANGED <<promised_id, pending_promise, msgs>>
       ELSE 
         /\ msgs' = msgs \cup {[type |-> "PrepareNack", to |-> msg.from, from |-> node, 
                                proposal_id |-> msg.proposal_id, promised_id |-> promised_id[node]]}
         /\ UNCHANGED <<promised_id, pending_promise>>
    /\ UNCHANGED <<proposal_id, next_proposal_number, promises_rcvd, leader, accepted_id, 
                  accepted_value, pending_accepted, final_value, final_proposal_id, final_acceptors, 
                  leader_uid, _nacks, proposed_value, leader_proposal_id, _acquiring, 
                  active_votes, last_accepted_id, leader_alive>>

RecvPromise(node, msg) ==
    /\ msg.type = "Promise"
    /\ msg.to = node
    /\ msg.from \in Nodes
    /\ next_proposal_number' = [next_proposal_number EXCEPT ![node] = ObserveProposal(node, msg.from, msg.proposal_id)]
    /\ IF leader[node] \/ msg.proposal_id /= proposal_id[node] \/ msg.from \in promises_rcvd[node]
       THEN UNCHANGED <<promises_rcvd, last_accepted_id, proposed_value, leader, leader_uid, 
                      leader_proposal_id, _acquiring, msgs>>
       ELSE
         LET new_promises == promises_rcvd[node] \cup {msg.from}
             updated_last_accepted == IF GreaterThan(msg.prev_accepted_id, last_accepted_id[node])
                                      THEN msg.prev_accepted_id
                                      ELSE last_accepted_id[node]
             updated_proposed_val == IF GreaterThan(msg.prev_accepted_id, last_accepted_id[node]) /\ msg.prev_accepted_value /= None
                                     THEN msg.prev_accepted_value
                                     ELSE proposed_value[node]
             is_now_leader == Cardinality(new_promises) = QuorumSize
         IN
           /\ promises_rcvd' = [promises_rcvd EXCEPT ![node] = new_promises]
           /\ last_accepted_id' = [last_accepted_id EXCEPT ![node] = updated_last_accepted]
           /\ proposed_value' = [proposed_value EXCEPT ![node] = updated_proposed_val]
           /\ IF is_now_leader
              THEN
                /\ leader' = [leader EXCEPT ![node] = TRUE]
                /\ leader_uid' = [leader_uid EXCEPT ![node] = node]
                /\ leader_proposal_id' = [leader_proposal_id EXCEPT ![node] = proposal_id[node]]
                /\ _acquiring' = [_acquiring EXCEPT ![node] = FALSE]
                /\ msgs' = msgs \cup 
                           (IF updated_proposed_val /= None
                            THEN {[type |-> "Accept", proposal_id |-> proposal_id[node], value |-> updated_proposed_val, from |-> node]}
                            ELSE {}) \cup
                           {[type |-> "Heartbeat", proposal_id |-> proposal_id[node], from |-> node]}
              ELSE
                /\ UNCHANGED <<leader, leader_uid, leader_proposal_id, _acquiring, msgs>>
    /\ UNCHANGED <<proposal_id, promised_id, accepted_id, accepted_value, pending_promise, 
                  pending_accepted, final_value, final_proposal_id, final_acceptors, _nacks, 
                  active_votes, leader_alive>>

RecvAcceptRequest(node, msg) ==
    /\ msg.type = "Accept"
    /\ msg.from \in Nodes
    /\ IF msg.proposal_id = accepted_id[node] /\ msg.value = accepted_value[node]
       THEN
         /\ msgs' = msgs \cup {[type |-> "Accepted", proposal_id |-> msg.proposal_id, value |-> msg.value, from |-> node]}
         /\ UNCHANGED <<promised_id, accepted_id, accepted_value, pending_accepted>>
       ELSE IF GreaterOrEqual(msg.proposal_id, promised_id[node])
       THEN
         IF pending_accepted[node] = None
         THEN
           /\ promised_id' = [promised_id EXCEPT ![node] = msg.proposal_id]
           /\ accepted_id' = [accepted_id EXCEPT ![node] = msg.proposal_id]
           /\ accepted_value' = [accepted_value EXCEPT ![node] = msg.value]
           /\ pending_accepted' = [pending_accepted EXCEPT ![node] = msg.from]
           /\ UNCHANGED msgs
         ELSE UNCHANGED <<promised_id, accepted_id, accepted_value, pending_accepted, msgs>>
       ELSE
         /\ msgs' = msgs \cup {[type |-> "AcceptNack", to |-> msg.from, from |-> node, 
                                proposal_id |-> msg.proposal_id, promised_id |-> promised_id[node]]}
         /\ UNCHANGED <<promised_id, accepted_id, accepted_value, pending_accepted>>
    /\ UNCHANGED <<proposal_id, next_proposal_number, promises_rcvd, leader, pending_promise, 
                  final_value, final_proposal_id, final_acceptors, leader_uid, _nacks, 
                  proposed_value, leader_proposal_id, _acquiring, active_votes, 
                  last_accepted_id, leader_alive>>

RecvAccepted(node, msg) ==
    /\ msg.type = "Accepted"
    /\ msg.from \in Nodes
    /\ IF final_value[node] /= None
       THEN 
         /\ IF msg.value = final_value[node]
            THEN final_acceptors' = [final_acceptors EXCEPT ![node] = final_acceptors[node] \cup {msg.from}]
            ELSE UNCHANGED final_acceptors
         /\ UNCHANGED <<final_value, final_proposal_id, active_votes>>
       ELSE
         LET has_voted == \exists v \in active_votes[node] : v.node = msg.from
         IN IF has_voted
            THEN
              LET old_v == CHOOSE v \in active_votes[node] : v.node = msg.from
              IN IF GreaterThan(msg.proposal_id, old_v.prop)
                 THEN
                   LET new_votes == (active_votes[node] \ {old_v}) \cup {[prop |-> msg.proposal_id, node |-> msg.from, val |-> msg.value]}
                       prop_votes == {v \in new_votes : v.prop = msg.proposal_id}
                   IN IF Cardinality(prop_votes) = QuorumSize
                      THEN
                        /\ final_value' = [final_value EXCEPT ![node] = msg.value]
                        /\ final_proposal_id' = [final_proposal_id EXCEPT ![node] = msg.proposal_id]
                        /\ final_acceptors' = [final_acceptors EXCEPT ![node] = {v.node : v \in prop_votes}]
                        /\ active_votes' = [active_votes EXCEPT ![node] = {}]
                      ELSE
                        /\ active_votes' = [active_votes EXCEPT ![node] = new_votes]
                        /\ UNCHANGED <<final_value, final_proposal_id, final_acceptors>>
                 ELSE UNCHANGED <<active_votes, final_value, final_proposal_id, final_acceptors>>
            ELSE
              LET new_votes == active_votes[node] \cup {[prop |-> msg.proposal_id, node |-> msg.from, val |-> msg.value]}
                  prop_votes == {v \in new_votes : v.prop = msg.proposal_id}
              IN IF Cardinality(prop_votes) = QuorumSize
                 THEN
                   /\ final_value' = [final_value EXCEPT ![node] = msg.value]
                   /\ final_proposal_id' = [final_proposal_id EXCEPT ![node] = msg.proposal_id]
                   /\ final_acceptors' = [final_acceptors EXCEPT ![node] = {v.node : v \in prop_votes}]
                   /\ active_votes' = [active_votes EXCEPT ![node] = {}]
                 ELSE
                   /\ active_votes' = [active_votes EXCEPT ![node] = new_votes]
                   /\ UNCHANGED <<final_value, final_proposal_id, final_acceptors>>
    /\ UNCHANGED <<proposal_id, next_proposal_number, promises_rcvd, leader, promised_id, 
                  accepted_id, accepted_value, pending_promise, pending_accepted, leader_uid, 
                  _nacks, proposed_value, leader_proposal_id, _acquiring, msgs, last_accepted_id, 
                  leader_alive>>

RecvPrepareNack(node, msg) ==
    /\ msg.type = "PrepareNack"
    /\ msg.to = node
    /\ msg.from \in Nodes
    /\ next_proposal_number' = [next_proposal_number EXCEPT ![node] = ObserveProposal(node, msg.from, msg.promised_id)]
    /\ IF _acquiring[node]
       THEN
         /\ leader' = [leader EXCEPT ![node] = FALSE]
         /\ promises_rcvd' = [promises_rcvd EXCEPT ![node] = {}]
         /\ proposal_id' = [proposal_id EXCEPT ![node] = [number |-> ObserveProposal(node, msg.from, msg.promised_id), uid |-> node]]
         /\ _nacks' = [_nacks EXCEPT ![node] = {}]
         /\ msgs' = msgs \cup {[type |-> "Prepare", 
                                proposal_id |-> [number |-> ObserveProposal(node, msg.from, msg.promised_id), uid |-> node], 
                                from |-> node]}
       ELSE
         /\ UNCHANGED <<leader, promises_rcvd, proposal_id, _nacks, msgs>>
    /\ UNCHANGED <<promised_id, accepted_id, accepted_value, pending_promise, pending_accepted, 
                  final_value, final_proposal_id, final_acceptors, leader_uid, proposed_value, 
                  leader_proposal_id, _acquiring, active_votes, last_accepted_id, leader_alive>>

RecvAcceptNack(node, msg) ==
    /\ msg.type = "AcceptNack"
    /\ msg.to = node
    /\ msg.from \in Nodes
    /\ IF msg.proposal_id = proposal_id[node]
       THEN
         LET new_nacks == _nacks[node] \cup {msg.from}
         IN
           /\ _nacks' = [_nacks EXCEPT ![node] = new_nacks]
           /\ IF leader[node] /\ Cardinality(new_nacks) >= QuorumSize
              THEN
                /\ leader' = [leader EXCEPT ![node] = FALSE]
                /\ promises_rcvd' = [promises_rcvd EXCEPT ![node] = {}]
                /\ leader_uid' = [leader_uid EXCEPT ![node] = None]
                /\ leader_proposal_id' = [leader_proposal_id EXCEPT ![node] = NilProposal]
                /\ next_proposal_number' = [next_proposal_number EXCEPT ![node] = ObserveProposal(node, msg.from, msg.promised_id)]
              ELSE
                /\ UNCHANGED <<leader, promises_rcvd, leader_uid, leader_proposal_id, next_proposal_number>>
       ELSE
         /\ UNCHANGED <<_nacks, leader, promises_rcvd, leader_uid, leader_proposal_id, next_proposal_number>>
    /\ UNCHANGED <<proposal_id, promised_id, accepted_id, accepted_value, pending_promise, 
                  pending_accepted, final_value, final_proposal_id, final_acceptors, proposed_value, 
                  _acquiring, active_votes, msgs, last_accepted_id, leader_alive>>

RecvHeartbeat(node, msg) ==
    /\ msg.type = "Heartbeat"
    /\ msg.from \in Nodes
    /\ IF GreaterThan(msg.proposal_id, leader_proposal_id[node])
       THEN
         /\ _acquiring' = [_acquiring EXCEPT ![node] = FALSE]
         /\ leader_uid' = [leader_uid EXCEPT ![node] = msg.from]
         /\ leader_proposal_id' = [leader_proposal_id EXCEPT ![node] = msg.proposal_id]
         /\ IF leader[node] /\ msg.from /= node
            THEN 
              /\ leader' = [leader EXCEPT ![node] = FALSE]
              /\ next_proposal_number' = [next_proposal_number EXCEPT ![node] = ObserveProposal(node, msg.from, msg.proposal_id)]
            ELSE UNCHANGED <<leader, next_proposal_number>>
         /\ leader_alive' = [leader_alive EXCEPT ![node] = TRUE]
       ELSE IF msg.proposal_id = leader_proposal_id[node]
       THEN
         /\ leader_alive' = [leader_alive EXCEPT ![node] = TRUE]
         /\ UNCHANGED <<_acquiring, leader_uid, leader_proposal_id, leader, next_proposal_number>>
       ELSE
         /\ UNCHANGED <<_acquiring, leader_uid, leader_proposal_id, leader, next_proposal_number, leader_alive>>
    /\ UNCHANGED <<proposal_id, promises_rcvd, promised_id, accepted_id, accepted_value, 
                  pending_promise, pending_accepted, final_value, final_proposal_id, 
                  final_acceptors, _nacks, proposed_value, active_votes, msgs, last_accepted_id>>

Next ==
    \/ \E n \in Nodes :
         \/ \E val \in Values : SetProposal(n, val)
         \/ PollLiveness(n)
         \/ Timeout(n)
         \/ Persisted(n)
         \/ \E msg \in msgs :
              \/ RecvPrepare(n, msg)
              \/ RecvPromise(n, msg)
              \/ RecvAcceptRequest(n, msg)
              \/ RecvAccepted(n, msg)
              \/ RecvPrepareNack(n, msg)
              \/ RecvAcceptNack(n, msg)
              \/ RecvHeartbeat(n, msg)

Spec == Init /\ [][Next]_vars

Agreement ==
    \forall n1, n2 \in Nodes :
        (final_value[n1] /= None /\ final_value[n2] /= None) => (final_value[n1] = final_value[n2])
=============================================================================