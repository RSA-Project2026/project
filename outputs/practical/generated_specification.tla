---- MODULE PracticalPaxos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Values, QUORUM_SIZE

VARIABLES 
    proposal_id,
    proposed_value,
    promises_rcvd,
    next_proposal_number,
    leader,
    last_accepted_id,
    promised_id,
    accepted_id,
    accepted_value,
    pending_promise,
    pending_accepted,
    learner_proposals,
    learner_last_pn,
    final_value,
    messages

vars == <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, 
          last_accepted_id, promised_id, accepted_id, accepted_value, pending_promise, 
          pending_accepted, learner_proposals, learner_last_pn, final_value, messages>>

None == "None"
QuorumSize == QUORUM_SIZE

\* Helper operators for lexicographical comparison of Proposal IDs: [number: Nat, uid: Nodes]
ID_GT(id1, id2) ==
  IF id1 = None THEN FALSE
  ELSE IF id2 = None THEN TRUE
  ELSE (id1.number > id2.number) \/ (id1.number = id2.number /\ id1.uid > id2.uid)

ID_GEQ(id1, id2) ==
  IF id1 = id2 THEN TRUE
  ELSE ID_GT(id1, id2)

\* Keep proposer's next_proposal_number up to date
UpdatedNPN(n, from_uid, pid) ==
  IF from_uid /= n /\ ID_GEQ(pid, [number |-> next_proposal_number[n], uid |-> n])
  THEN pid.number + 1
  ELSE next_proposal_number[n]

Init == 
    /\ proposal_id = [n \in Nodes |-> None]
    /\ proposed_value = [n \in Nodes |-> None]
    /\ promises_rcvd = [n \in Nodes |-> {}]
    /\ next_proposal_number = [n \in Nodes |-> 1]
    /\ leader = [n \in Nodes |-> FALSE]
    /\ last_accepted_id = [n \in Nodes |-> None]
    /\ promised_id = [n \in Nodes |-> None]
    /\ accepted_id = [n \in Nodes |-> None]
    /\ accepted_value = [n \in Nodes |-> None]
    /\ pending_promise = [n \in Nodes |-> None]
    /\ pending_accepted = [n \in Nodes |-> None]
    /\ learner_proposals = [n \in Nodes |-> {}]
    /\ learner_last_pn = [n \in Nodes |-> [m \in Nodes |-> None]]
    /\ final_value = [n \in Nodes |-> None]
    /\ messages = {}

\* Proposer.set_proposal
SetProposal(n, val) ==
  /\ proposed_value[n] = None
  /\ proposed_value' = [proposed_value EXCEPT ![n] = val]
  /\ IF leader[n]
     THEN messages' = messages \cup {[type |-> "Accept", from |-> n, proposal_id |-> proposal_id[n], value |-> val]}
     ELSE UNCHANGED messages
  /\ UNCHANGED <<proposal_id, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                 promised_id, accepted_id, accepted_value, pending_promise,
                 pending_accepted, learner_proposals, learner_last_pn, final_value>>

\* Proposer.prepare
Prepare(n) ==
  LET new_pid == [number |-> next_proposal_number[n], uid |-> n]
  IN  /\ leader' = [leader EXCEPT ![n] = FALSE]
      /\ promises_rcvd' = [promises_rcvd EXCEPT ![n] = {}]
      /\ proposal_id' = [proposal_id EXCEPT ![n] = new_pid]
      /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = next_proposal_number[n] + 1]
      /\ messages' = messages \cup {[type |-> "Prepare", from |-> n, proposal_id |-> new_pid]}
      /\ UNCHANGED <<proposed_value, last_accepted_id, promised_id, accepted_id, accepted_value,
                     pending_promise, pending_accepted, learner_proposals, learner_last_pn, final_value>>

\* Proposer.recv_promise
RecvPromise(n, msg) ==
  /\ msg \in messages
  /\ msg.type = "Promise"
  /\ msg.to = n
  LET 
    new_npn == UpdatedNPN(n, msg.from, msg.proposal_id)
  IN
    IF leader[n] \/ msg.proposal_id /= proposal_id[n] \/ msg.from \in promises_rcvd[n]
    THEN 
      /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
      /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                     promised_id, accepted_id, accepted_value, pending_promise,
                     pending_accepted, learner_proposals, learner_last_pn, final_value, messages>>
    ELSE
      LET
        new_promises == promises_rcvd[n] \cup {msg.from}
        updates_accepted == ID_GT(msg.prev_accepted_id, last_accepted_id[n])
        new_last_accepted_id == IF updates_accepted THEN msg.prev_accepted_id ELSE last_accepted_id[n]
        new_proposed_value == IF updates_accepted /\ msg.prev_accepted_value /= None 
                              THEN msg.prev_accepted_value 
                              ELSE proposed_value[n]
        became_leader == (Cardinality(new_promises) = QuorumSize)
        new_leader == became_leader
        send_accept == became_leader /\ new_proposed_value /= None
        new_msg == IF send_accept 
                   THEN messages \cup {[type |-> "Accept", from |-> n, proposal_id |-> proposal_id[n], value |-> new_proposed_value]}
                   ELSE messages
      IN
        /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
        /\ promises_rcvd' = [promises_rcvd EXCEPT ![n] = new_promises]
        /\ last_accepted_id' = [last_accepted_id EXCEPT ![n] = new_last_accepted_id]
        /\ proposed_value' = [proposed_value EXCEPT ![n] = new_proposed_value]
        /\ leader' = [leader EXCEPT ![n] = new_leader]
        /\ messages' = new_msg
        /\ UNCHANGED <<proposal_id, promised_id, accepted_id, accepted_value,
                       pending_promise, pending_accepted, learner_proposals, learner_last_pn, final_value>>

\* Proposer.recv_prepare_nack
RecvPrepareNack(n, msg) ==
  /\ msg \in messages
  /\ msg.type = "PrepareNack"
  /\ msg.to = n
  /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = UpdatedNPN(n, msg.from, msg.promised_id)]
  /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                 promised_id, accepted_id, accepted_value, pending_promise,
                 pending_accepted, learner_proposals, learner_last_pn, final_value, messages>>

\* Acceptor.recv_prepare / Node.recv_prepare (combined atomic step)
RecvPrepare(n, msg) ==
  /\ msg \in messages
  /\ msg.type = "Prepare"
  LET 
    new_npn == UpdatedNPN(n, msg.from, msg.proposal_id)
  IN
    IF msg.proposal_id = promised_id[n]
    THEN 
      /\ messages' = messages \cup {[
           type |-> "Promise", 
           from |-> n, 
           to |-> msg.from, 
           proposal_id |-> msg.proposal_id, 
           prev_accepted_id |-> accepted_id[n], 
           prev_accepted_value |-> accepted_value[n]
         ]}
      /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
      /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                     promised_id, accepted_id, accepted_value, pending_promise,
                     pending_accepted, learner_proposals, learner_last_pn, final_value>>
    ELSE IF ID_GT(msg.proposal_id, promised_id[n])
    THEN
      IF pending_promise[n] = None
      THEN
        /\ promised_id' = [promised_id EXCEPT ![n] = msg.proposal_id]
        /\ pending_promise' = [pending_promise EXCEPT ![n] = msg.from]
        /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
        /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                       accepted_id, accepted_value, pending_accepted, learner_proposals, 
                       learner_last_pn, final_value, messages>>
      ELSE
        /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
        /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                       promised_id, accepted_id, accepted_value, pending_promise,
                       pending_accepted, learner_proposals, learner_last_pn, final_value, messages>>
    ELSE
      /\ messages' = messages \cup {[
           type |-> "PrepareNack", 
           from |-> n, 
           to |-> msg.from, 
           proposal_id |-> msg.proposal_id, 
           promised_id |-> promised_id[n]
         ]}
      /\ next_proposal_number' = [next_proposal_number EXCEPT ![n] = new_npn]
      /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, leader, last_accepted_id,
                     promised_id, accepted_id, accepted_value, pending_promise,
                     pending_accepted, learner_proposals, learner_last_pn, final_value>>

\* Acceptor.recv_accept_request
RecvAcceptRequest(n, msg) ==
  /\ msg \in messages
  /\ msg.type = "Accept"
  /\ IF msg.proposal_id = accepted_id[n] /\ msg.value = accepted_value[n]
     THEN
       /\ messages' = messages \cup {[
            type |-> "Accepted",
            from |-> n,
            proposal_id |-> msg.proposal_id,
            value |-> msg.value
          ]}
       /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                      promised_id, accepted_id, accepted_value, pending_promise,
                      pending_accepted, learner_proposals, learner_last_pn, final_value>>
     ELSE IF ID_GEQ(msg.proposal_id, promised_id[n])
     THEN
       IF pending_accepted[n] = None
       THEN
         /\ promised_id' = [promised_id EXCEPT ![n] = msg.proposal_id]
         /\ accepted_id' = [accepted_id EXCEPT ![n] = msg.proposal_id]
         /\ accepted_value' = [accepted_value EXCEPT ![n] = msg.value]
         /\ pending_accepted' = [pending_accepted EXCEPT ![n] = msg.from]
         /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                        pending_promise, learner_proposals, learner_last_pn, final_value, messages>>
       ELSE
         UNCHANGED vars
     ELSE
       /\ messages' = messages \cup {[
            type |-> "AcceptNack",
            from |-> n,
            to |-> msg.from,
            proposal_id |-> msg.proposal_id,
            promised_id |-> promised_id[n]
          ]}
       /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                      promised_id, accepted_id, accepted_value, pending_promise,
                      pending_accepted, learner_proposals, learner_last_pn, final_value>>

\* Acceptor.persisted
Persisted(n) ==
  /\ (pending_promise[n] /= None \/ pending_accepted[n] /= None)
  LET
    promise_msg == IF pending_promise[n] /= None
                   THEN {[
                     type |-> "Promise",
                     from |-> n,
                     to |-> pending_promise[n],
                     proposal_id |-> promised_id[n],
                     prev_accepted_id |-> accepted_id[n],
                     prev_accepted_value |-> accepted_value[n]
                   ]}
                   ELSE {}
    accepted_msg == IF pending_accepted[n] /= None
                    THEN {[
                      type |-> "Accepted",
                      from |-> n,
                      proposal_id |-> accepted_id[n],
                      value |-> accepted_value[n]
                    ]}
                    ELSE {}
  IN
    /\ messages' = messages \cup promise_msg \cup accepted_msg
    /\ pending_promise' = [pending_promise EXCEPT ![n] = None]
    /\ pending_accepted' = [pending_accepted EXCEPT ![n] = None]
    /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                   promised_id, accepted_id, accepted_value, learner_proposals, learner_last_pn, final_value>>

\* Learner.recv_accepted
RecvAccepted(n, msg) ==
  /\ msg \in messages
  /\ msg.type = "Accepted"
  /\ IF final_value[n] /= None
     THEN 
       UNCHANGED vars
     ELSE
       LET 
         last_pn == learner_last_pn[n][msg.from]
       IN
         IF last_pn /= None /\ ID_GEQ(last_pn, msg.proposal_id)
         THEN
           UNCHANGED vars
         ELSE
           LET
             existing_record_set == {r \in learner_proposals[n] : r.id = msg.proposal_id}
           IN
             \* Enforce single-value-per-proposal assertion
             /\ \A r \in existing_record_set : r.value = msg.value
             /\ LET
                  existing_record == 
                    IF existing_record_set /= {}
                    THEN CHOOSE r \in existing_record_set : TRUE
                    ELSE [id |-> msg.proposal_id, votes |-> {}, value |-> msg.value]
                  new_record == [existing_record EXCEPT !.votes = existing_record.votes \cup {msg.from}]
                  new_proposals == (learner_proposals[n] \ existing_record_set) \cup {new_record}
                  is_resolved == (Cardinality(new_record.votes) = QuorumSize)
                  new_final_value == IF is_resolved THEN msg.value ELSE final_value[n]
                IN
                  /\ learner_last_pn' = [learner_last_pn EXCEPT ![n] = [learner_last_pn[n] EXCEPT ![msg.from] = msg.proposal_id]]
                  /\ learner_proposals' = [learner_proposals EXCEPT ![n] = new_proposals]
                  /\ final_value' = [final_value EXCEPT ![n] = new_final_value]
                  /\ UNCHANGED <<proposal_id, proposed_value, promises_rcvd, next_proposal_number, leader, last_accepted_id,
                                 promised_id, accepted_id, accepted_value, pending_promise,
                                 pending_accepted, messages>>

\* Acceptor.recover (Crash recovery: transient state reset)
CrashAndRecover(n) ==
  /\ (pending_promise[n] /= None \/ pending_accepted[n] /= None \/ leader[n] = TRUE \/ promises_rcvd[n] /= {})
  /\ pending_promise' = [pending_promise EXCEPT ![n] = None]
  /\ pending_accepted' = [pending_accepted EXCEPT ![n] = None]
  /\ leader' = [leader EXCEPT ![n] = FALSE]
  /\ promises_rcvd' = [promises_rcvd EXCEPT ![n] = {}]
  /\ UNCHANGED <<proposal_id, proposed_value, next_proposal_number, last_accepted_id,
                 promised_id, accepted_id, accepted_value, learner_proposals, learner_last_pn, final_value, messages>>

Next == 
  \/ \E n \in Nodes, val \in Values : SetProposal(n, val)
  \/ \E n \in Nodes : Prepare(n)
  \/ \E n \in Nodes, msg \in messages : RecvPromise(n, msg)
  \/ \E n \in Nodes, msg \in messages : RecvPrepareNack(n, msg)
  \/ \E n \in Nodes, msg \in messages : RecvPrepare(n, msg)
  \/ \E n \in Nodes, msg \in messages : RecvAcceptRequest(n, msg)
  \/ \E n \in Nodes : Persisted(n)
  \/ \E n \in Nodes, msg \in messages : RecvAccepted(n, msg)
  \/ \E n \in Nodes : CrashAndRecover(n)

Spec == Init /\ [][Next]_vars

\* Safety Property: Agreement
Agreement ==
  \A n1, n2 \in Nodes :
    (final_value[n1] /= None /\ final_value[n2] /= None) => (final_value[n1] = final_value[n2])

====