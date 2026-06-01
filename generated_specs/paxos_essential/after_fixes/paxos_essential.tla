---- MODULE paxos_essential ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proposers, Acceptors, Learners, Values, QuorumSize, Nil

VARIABLES 
    proposed_value,
    proposal_id,
    last_accepted_id,
    next_proposal_number,
    promises_rcvd,
    promised_id,
    accepted_id,
    accepted_value,
    accepted_map,
    final_value,
    final_proposal_id,
    messages

vars == <<proposed_value, proposal_id, last_accepted_id, next_proposal_number, 
          promises_rcvd, promised_id, accepted_id, accepted_value, 
          accepted_map, final_value, final_proposal_id, messages>>

-----------------------------------------------------------------------------

RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN << >>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN << x >> \o SetToSeq(S \ {x})

ProposerSeq == SetToSeq(Proposers)

Proposer_GT(u1, u2) ==
    LET index(u) == CHOOSE i \in 1..Len(ProposerSeq) : ProposerSeq[i] = u
    IN index(u1) > index(u2)

\* Helper operators for Proposal ID comparisons.
\* Python tuples are compared lexicographically: (number, uid).
\* Nil acts as None (lower than any valid proposal).
Proposal_GT(p1, p2) ==
    IF p1 = Nil THEN FALSE
    ELSE IF p2 = Nil THEN TRUE
    ELSE (p1.number > p2.number) \/ (p1.number = p2.number /\ Proposer_GT(p1.uid, p2.uid))

Proposal_GE(p1, p2) ==
    p1 = p2 \/ Proposal_GT(p1, p2)

-----------------------------------------------------------------------------

Init == 
    /\ proposed_value = [p \in Proposers |-> Nil]
    /\ proposal_id = [p \in Proposers |-> Nil]
    /\ last_accepted_id = [p \in Proposers |-> Nil]
    /\ next_proposal_number = [p \in Proposers |-> 1]
    /\ promises_rcvd = [p \in Proposers |-> {}]
    /\ promised_id = [a \in Acceptors |-> Nil]
    /\ accepted_id = [a \in Acceptors |-> Nil]
    /\ accepted_value = [a \in Acceptors |-> Nil]
    /\ accepted_map = [l \in Learners |-> {}]
    /\ final_value = [l \in Learners |-> Nil]
    /\ final_proposal_id = [l \in Learners |-> Nil]
    /\ messages = {}

-----------------------------------------------------------------------------

\* Proposer.set_proposal
SetProposal(p, v) ==
    /\ proposed_value[p] = Nil
    /\ proposed_value' = [proposed_value EXCEPT ![p] = v]
    /\ UNCHANGED <<proposal_id, last_accepted_id, next_proposal_number, promises_rcvd,
                  promised_id, accepted_id, accepted_value,
                  accepted_map, final_value, final_proposal_id, messages>>

\* Proposer.prepare
Prepare(p) ==
    LET new_id == [number |-> next_proposal_number[p], uid |-> p]
    IN
    /\ promises_rcvd' = [promises_rcvd EXCEPT ![p] = {}]
    /\ proposal_id' = [proposal_id EXCEPT ![p] = new_id]
    /\ next_proposal_number' = [next_proposal_number EXCEPT ![p] = next_proposal_number[p] + 1]
    /\ messages' = messages \cup {[type |-> "prepare", proposal_id |-> new_id]}
    /\ UNCHANGED <<proposed_value, last_accepted_id, promised_id, accepted_id, accepted_value, 
                  accepted_map, final_value, final_proposal_id>>

\* Proposer.recv_promise
RecvPromise(p, msg) ==
    /\ msg \in messages
    /\ msg.type = "promise"
    /\ msg.to = p
    /\ msg.proposal_id = proposal_id[p]
    /\ msg.from \notin promises_rcvd[p]
    /\ LET 
           new_promises == promises_rcvd[p] \cup {msg.from}
           updated_last_accepted_id == 
               IF Proposal_GT(msg.prev_accepted_id, last_accepted_id[p]) 
               THEN msg.prev_accepted_id 
               ELSE last_accepted_id[p]
           updated_proposed_value == 
               IF Proposal_GT(msg.prev_accepted_id, last_accepted_id[p]) /\ msg.prev_accepted_value /= Nil 
               THEN msg.prev_accepted_value 
               ELSE proposed_value[p]
           \* Broadcast Accept request if quorum achieved
           send_accept_msg == 
               IF Cardinality(new_promises) = QuorumSize /\ updated_proposed_value /= Nil
               THEN {[type |-> "accept", proposal_id |-> proposal_id[p], value |-> updated_proposed_value]}
               ELSE {}
       IN
           /\ promises_rcvd' = [promises_rcvd EXCEPT ![p] = new_promises]
           /\ last_accepted_id' = [last_accepted_id EXCEPT ![p] = updated_last_accepted_id]
           /\ proposed_value' = [proposed_value EXCEPT ![p] = updated_proposed_value]
           /\ messages' = messages \cup send_accept_msg
           /\ UNCHANGED <<proposal_id, next_proposal_number, promised_id, accepted_id, 
                         accepted_value, accepted_map, final_value, final_proposal_id>>

\* Acceptor.recv_prepare
AcceptorRecvPrepare(a, msg) ==
    /\ msg \in messages
    /\ msg.type = "prepare"
    /\ Proposal_GE(msg.proposal_id, promised_id[a])
    /\ promised_id' = [promised_id EXCEPT ![a] = msg.proposal_id]
    /\ messages' = messages \cup {[
                      type |-> "promise",
                      to |-> msg.proposal_id.uid,
                      from |-> a,
                      proposal_id |-> msg.proposal_id,
                      prev_accepted_id |-> accepted_id[a],
                      prev_accepted_value |-> accepted_value[a]
                   ]}
    /\ UNCHANGED <<proposed_value, proposal_id, last_accepted_id, next_proposal_number, 
                  promises_rcvd, accepted_id, accepted_value, accepted_map, 
                  final_value, final_proposal_id>>

\* Acceptor.recv_accept_request
AcceptorRecvAccept(a, msg) ==
    /\ msg \in messages
    /\ msg.type = "accept"
    /\ Proposal_GE(msg.proposal_id, promised_id[a])
    /\ promised_id' = [promised_id EXCEPT ![a] = msg.proposal_id]
    /\ accepted_id' = [accepted_id EXCEPT ![a] = msg.proposal_id]
    /\ accepted_value' = [accepted_value EXCEPT ![a] = msg.value]
    /\ messages' = messages \cup {[
                      type |-> "accepted",
                      from |-> a,
                      proposal_id |-> msg.proposal_id,
                      value |-> msg.value
                   ]}
    /\ UNCHANGED <<proposed_value, proposal_id, last_accepted_id, next_proposal_number, 
                  promises_rcvd, accepted_map, final_value, final_proposal_id>>

\* Learner.recv_accepted
LearnerRecvAccepted(l, msg) ==
    /\ msg \in messages
    /\ msg.type = "accepted"
    /\ final_value[l] = Nil
    /\ LET 
           last_p == IF \E r \in accepted_map[l] : r.acceptor = msg.from
                     THEN (CHOOSE r \in accepted_map[l] : r.acceptor = msg.from).proposal
                     ELSE Nil
       IN
           /\ Proposal_GT(msg.proposal_id, last_p)
           /\ LET 
                  new_map == (accepted_map[l] \ { r \in accepted_map[l] : r.acceptor = msg.from }) \cup
                             {[acceptor |-> msg.from, proposal |-> msg.proposal_id, value |-> msg.value]}
                  acceptors_for_proposal == { r.acceptor : r \in {x \in new_map : x.proposal = msg.proposal_id} }
              IN
                  IF Cardinality(acceptors_for_proposal) >= QuorumSize
                  THEN
                      /\ final_value' = [final_value EXCEPT ![l] = msg.value]
                      /\ final_proposal_id' = [final_proposal_id EXCEPT ![l] = msg.proposal_id]
                      /\ accepted_map' = [accepted_map EXCEPT ![l] = {}]
                  ELSE
                      /\ final_value' = final_value
                      /\ final_proposal_id' = final_proposal_id
                      /\ accepted_map' = [accepted_map EXCEPT ![l] = new_map]
           /\ UNCHANGED <<proposed_value, proposal_id, last_accepted_id, next_proposal_number, 
                         promises_rcvd, promised_id, accepted_id, accepted_value, messages>>

-----------------------------------------------------------------------------

Next ==
    \/ \E p \in Proposers, v \in Values : SetProposal(p, v)
    \/ \E p \in Proposers : Prepare(p)
    \/ \E p \in Proposers, msg \in messages : RecvPromise(p, msg)
    \/ \E a \in Acceptors, msg \in messages : AcceptorRecvPrepare(a, msg)
    \/ \E a \in Acceptors, msg \in messages : AcceptorRecvAccept(a, msg)
    \/ \E l \in Learners, msg \in messages : LearnerRecvAccepted(l, msg)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Safety Properties

\* Learner.complete property helper
LearnerComplete(l) == final_proposal_id[l] /= Nil

TypeOK ==
    /\ proposed_value \in [Proposers -> Values \cup {Nil}]
    /\ proposal_id \in [Proposers -> [number: Nat, uid: Proposers] \cup {Nil}]
    /\ last_accepted_id \in [Proposers -> [number: Nat, uid: Proposers] \cup {Nil}]
    /\ next_proposal_number \in [Proposers -> Nat]
    /\ promises_rcvd \in [Proposers -> SUBSET Acceptors]
    /\ promised_id \in [Acceptors -> [number: Nat, uid: Proposers] \cup {Nil}]
    /\ accepted_id \in [Acceptors -> [number: Nat, uid: Proposers] \cup {Nil}]
    /\ accepted_value \in [Acceptors -> Values \cup {Nil}]
    /\ accepted_map \in [Learners -> SUBSET [acceptor: Acceptors, proposal: [number: Nat, uid: Proposers], value: Values]]
    /\ final_value \in [Learners -> Values \cup {Nil}]
    /\ final_proposal_id \in [Learners -> [number: Nat, uid: Proposers] \cup {Nil}]

\* Consensus Agreement Property: No two Learners decide on different values.
Agreement ==
    \A l1, l2 \in Learners :
        (final_value[l1] /= Nil /\ final_value[l2] /= Nil) 
        => (final_value[l1] = final_value[l2])

=============================================================================