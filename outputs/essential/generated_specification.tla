---- MODULE Paxos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Proposers,    \* Set of all Proposer UIDs
    Acceptors,    \* Set of all Acceptor UIDs
    Learners,     \* Set of all Learner UIDs
    Values,       \* Set of all proposed consensus values
    QuorumSize    \* Size of the quorum required for consensus (e.g. 2 for 3 nodes)

VARIABLES 
    proposer_state,
    acceptor_state,
    learner_state,
    network

vars == <<proposer_state, acceptor_state, learner_state, network>>

\* Helper values representing None
NoneValue == "none_value"
NoneID == [number |-> -1, uid |-> "none_uid"]

\* Helper to lexicographically compare Proposal IDs: [number, uid]
IDGreater(id1, id2) ==
    IF id1 = NoneID THEN FALSE
    ELSE IF id2 = NoneID THEN TRUE
    ELSE id1.number > id2.number \/ (id1.number = id2.number /\ id1.uid > id2.uid)

IDGreaterOrEqual(id1, id2) ==
    id1 = id2 \/ IDGreater(id1, id2)

-----------------------------------------------------------------------------

Init == 
    /\ proposer_state = [p \in Proposers |-> [
            proposed_value |-> NoneValue,
            proposal_id |-> NoneID,
            last_accepted_id |-> NoneID,
            next_proposal_number |-> 1,
            promises_rcvd |-> {}
       ]]
    /\ acceptor_state = [a \in Acceptors |-> [
            promised_id |-> NoneID,
            accepted_id |-> NoneID,
            accepted_value |-> NoneValue
       ]]
    /\ learner_state = [l \in Learners |-> [
            final_value |-> NoneValue,
            final_proposal_id |-> NoneID,
            proposals |-> [pid \in {} |-> [accept_count |-> 0, retain_count |-> 0, value |-> NoneValue]],
            acceptors |-> [a \in Acceptors |-> NoneID]
       ]]
    /\ network = {}

-----------------------------------------------------------------------------
\* Core Proposer Actions

\* Client interface equivalent to self.set_proposal(value)
SetProposal(p, val) ==
    /\ proposer_state[p].proposed_value = NoneValue
    /\ proposer_state' = [proposer_state EXCEPT ![p].proposed_value = val]
    /\ UNCHANGED <<acceptor_state, learner_state, network>>

\* Proposer initiates a new round: self.prepare()
Prepare(p) ==
    LET new_id == [number |-> proposer_state[p].next_proposal_number, uid |-> p]
        new_msg == [type        |-> "Prepare", 
                    proposal_id |-> new_id, 
                    from_uid    |-> p]
    IN
    /\ proposer_state' = [proposer_state EXCEPT 
                            ![p].promises_rcvd = {},
                            ![p].proposal_id = new_id,
                            ![p].next_proposal_number = proposer_state[p].next_proposal_number + 1]
    /\ network' = network \cup {new_msg}
    /\ UNCHANGED <<acceptor_state, learner_state>>

\* Proposer receives a promise: self.recv_promise(...)
ReceivePromise(p) ==
    \E msg \in network :
        /\ msg.type = "Promise"
        /\ msg.to_uid = p
        \* Ignore if duplicate or if proposal ID doesn't match current round
        /\ msg.proposal_id = proposer_state[p].proposal_id
        /\ msg.from_uid \notin proposer_state[p].promises_rcvd
        /\ LET 
            new_promises == proposer_state[p].promises_rcvd \cup {msg.from_uid}
            
            \* Track the highest-numbered accepted value returned by any Acceptor
            updates_value == IDGreater(msg.prev_accepted_id, proposer_state[p].last_accepted_id)
            new_last_accepted_id == IF updates_value THEN msg.prev_accepted_id ELSE proposer_state[p].last_accepted_id
            new_proposed_value == IF updates_value /\ msg.prev_accepted_value /= NoneValue
                                  THEN msg.prev_accepted_value
                                  ELSE proposer_state[p].proposed_value
            
            \* Broadcast "Accept" request if quorum is achieved
            reached_quorum == (Cardinality(new_promises) = QuorumSize)
            accept_msg == [type        |-> "Accept", 
                           proposal_id |-> proposer_state[p].proposal_id, 
                           value       |-> new_proposed_value,
                           from_uid    |-> p]
            new_network == IF reached_quorum /\ new_proposed_value /= NoneValue
                           THEN network \cup {accept_msg}
                           ELSE network
           IN
           /\ proposer_state' = [proposer_state EXCEPT 
                                    ![p].promises_rcvd = new_promises,
                                    ![p].last_accepted_id = new_last_accepted_id,
                                    ![p].proposed_value = new_proposed_value]
           /\ network' = new_network
           /\ UNCHANGED <<acceptor_state, learner_state>>

-----------------------------------------------------------------------------
\* Core Acceptor Actions

\* Acceptor processes prepare request: self.recv_prepare(...)
ReceivePrepare(a) ==
    \E msg \in network :
        /\ msg.type = "Prepare"
        /\ IDGreaterOrEqual(msg.proposal_id, acceptor_state[a].promised_id)
        /\ LET 
            new_promised_id == msg.proposal_id
            promise_msg == [type                |-> "Promise",
                            to_uid              |-> msg.from_uid,
                            from_uid            |-> a,
                            proposal_id         |-> msg.proposal_id,
                            prev_accepted_id    |-> acceptor_state[a].accepted_id,
                            prev_accepted_value |-> acceptor_state[a].accepted_value]
           IN
           /\ acceptor_state' = [acceptor_state EXCEPT ![a].promised_id = new_promised_id]
           /\ network' = network \cup {promise_msg}
           /\ UNCHANGED <<proposer_state, learner_state>>

\* Acceptor processes accept request: self.recv_accept_request(...)
ReceiveAcceptRequest(a) ==
    \E msg \in network :
        /\ msg.type = "Accept"
        /\ IDGreaterOrEqual(msg.proposal_id, acceptor_state[a].promised_id)
        /\ LET 
            accepted_msg == [type           |-> "Accepted",
                             proposal_id    |-> msg.proposal_id,
                             accepted_value |-> msg.value,
                             from_uid       |-> a]
           IN
           /\ acceptor_state' = [acceptor_state EXCEPT 
                                    ![a].promised_id = msg.proposal_id,
                                    ![a].accepted_id = msg.proposal_id,
                                    ![a].accepted_value = msg.value]
           /\ network' = network \cup {accepted_msg}
           /\ UNCHANGED <<proposer_state, learner_state>>

-----------------------------------------------------------------------------
\* Core Learner Action

\* Learner processes an accepted message: self.recv_accepted(...)
ReceiveAccepted(l) ==
    \E msg \in network :
        /\ msg.type = "Accepted"
        /\ learner_state[l].final_value = NoneValue  \* Ignore if already resolved
        /\ LET 
            from_uid == msg.from_uid
            proposal_id == msg.proposal_id
            accepted_value == msg.accepted_value
            last_pn == learner_state[l].acceptors[from_uid]
           IN
           \* Process only if strictly newer than last proposal accepted by this acceptor
           /\ IDGreater(proposal_id, last_pn)
           /\ LET 
                \* Update acceptor's tracking map
                new_acceptors == [learner_state[l].acceptors EXCEPT ![from_uid] = proposal_id]
                
                \* Clean up / Decrement old proposal entry if one existed
                proposals_after_old == 
                    IF last_pn /= NoneID /\ last_pn \in DOMAIN learner_state[l].proposals
                    THEN
                        LET old_entry == learner_state[l].proposals[last_pn]
                            new_retain == old_entry.retain_count - 1
                        IN
                        IF new_retain = 0
                        THEN [pid \in (DOMAIN learner_state[l].proposals \ {last_pn}) |-> learner_state[l].proposals[pid]]
                        ELSE [learner_state[l].proposals EXCEPT ![last_pn].retain_count = new_retain]
                    ELSE learner_state[l].proposals
                
                \* Initialize proposal tracking record if not exists
                proposals_with_new ==
                    IF proposal_id \in DOMAIN proposals_after_old
                    THEN proposals_after_old
                    ELSE [pid \in (DOMAIN proposals_after_old \cup {proposal_id}) |-> 
                            IF pid = proposal_id 
                            THEN [accept_count |-> 0, retain_count |-> 0, value |-> accepted_value]
                            ELSE proposals_after_old[pid]]
                
                \* Safety assert check: value mismatch check
                _assert_ok == accepted_value = proposals_with_new[proposal_id].value
                
                \* Increment current counts
                current_entry == proposals_with_new[proposal_id]
                new_accept_count == current_entry.accept_count + 1
                new_retain_count == current_entry.retain_count + 1
                updated_entry == [accept_count |-> new_accept_count, 
                                  retain_count |-> new_retain_count, 
                                  value        |-> accepted_value]
                
                final_proposals == [proposals_with_new EXCEPT ![proposal_id] = updated_entry]
                
                \* Check for quorum resolution
                quorum_reached == (new_accept_count = QuorumSize)
                
                \* If consensus is resolved, clean up all local trackers as in Python code
                next_learner_record ==
                    IF quorum_reached
                    THEN [
                        final_value       |-> accepted_value,
                        final_proposal_id |-> proposal_id,
                        proposals         |-> [pid \in {} |-> [accept_count |-> 0, retain_count |-> 0, value |-> NoneValue]],
                        acceptors         |-> [a \in Acceptors |-> NoneID]
                    ]
                    ELSE [
                        final_value       |-> NoneValue,
                        final_proposal_id |-> NoneID,
                        proposals         |-> final_proposals,
                        acceptors         |-> new_acceptors
                    ]
              IN
              /\ _assert_ok
              /\ learner_state' = [learner_state EXCEPT ![l] = next_learner_record]
              /\ UNCHANGED <<proposer_state, acceptor_state, network>>

-----------------------------------------------------------------------------

Next == 
    \/ \E p \in Proposers, v \in Values : SetProposal(p, v)
    \/ \E p \in Proposers : Prepare(p)
    \/ \E p \in Proposers : ReceivePromise(p)
    \/ \E a \in Acceptors : ReceivePrepare(a)
    \/ \E a \in Acceptors : ReceiveAcceptRequest(a)
    \/ \E l \in Learners  : ReceiveAccepted(l)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Correctness Properties

\* Agreement: No two learners decide on different final values
Agreement ==
    \A l1, l2 \in Learners :
        (learner_state[l1].final_value /= NoneValue /\ learner_state[l2].final_value /= NoneValue)
        => (learner_state[l1].final_value = learner_state[l2].final_value)

====