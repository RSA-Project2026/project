'''
This module is a practical Paxos implementation, implementing only the essential 
Paxos components and adds functionality required for most practical 
uses of the algorithm. 
'''


import collections

# In order for the Paxos algorithm to function, all proposal ids must be
# unique. A simple way to ensure this is to include the proposer's UID
# in the proposal id. This prevents the possibility of two Proposers
# from proposing different values for the same proposal ID.
#
# Python tuples are a simple mechanism that allow the proposal number
# and the UID to be combined easily and in a manner that supports
# comparison. To simplify the code, we'll use "namedtuple" instances
# from the collections module which allows us to write
# "proposal_id.number" instead of "proposal_id[0]".
#
ProposalID = collections.namedtuple('ProposalID', ['number', 'uid'])


class Messenger:

    def send_prepare(self, proposal_id):
        '''
        Broadcasts a Prepare message to all Acceptors
        '''

    def send_promise(self, proposer_uid, proposal_id, previous_id, accepted_value):
        '''
        Sends a Promise message to the specified Proposer
        '''

    def send_accept(self, proposal_id, proposal_value):
        '''
        Broadcasts an Accept! message to all Acceptors
        '''

    def send_accepted(self, proposal_id, accepted_value):
        '''
        Broadcasts an Accepted message to all Learners
        '''

    def on_resolution(self, proposal_id, value):
        '''
        Called when a resolution is reached
        '''
    
    def send_prepare_nack(self, to_uid, proposal_id, promised_id):
        '''
        Sends a Prepare Nack message for the proposal to the specified node
        '''

    def send_accept_nack(self, to_uid, proposal_id, promised_id):
        '''
        Sends a Accept! Nack message for the proposal to the specified node
        '''

    def on_leadership_acquired(self):
        '''
        Called when leadership has been acquired. This is not a guaranteed
        position. Another node may assume leadership at any time and it's
        even possible that another may have successfully done so before this
        callback is executed. Use this method with care.

        The safe way to guarantee leadership is to use a full Paxos instance
        with the resolution value being the UID of the leader node. To avoid
        potential issues arising from timing and/or failure, the election
        result may be restricted to a certain time window. Prior to the end of
        the window the leader may attempt to re-elect itself to extend its
        term in office.
        '''

        
class Proposer(object):

    messenger            = None
    proposer_uid         = None
    quorum_size          = None

    proposed_value       = None
    proposal_id          = None 
    last_accepted_id     = None
    next_proposal_number = 1
    promises_rcvd        = None
    
    leader = False 
    active = True  

    
    def set_proposal(self, value):
        '''
        Sets the proposal value for this node iff this node is not already aware of
        another proposal having already been accepted. 
        '''
        if self.proposed_value is None:
            self.proposed_value = value

            if self.leader and self.active:
                self.messenger.send_accept( self.proposal_id, value )


    def prepare(self, increment_proposal_number=True):
        '''
        Sends a prepare request to all Acceptors as the first step in
        attempting to acquire leadership of the Paxos instance. If the
        'increment_proposal_number' argument is True (the default), the
        proposal id will be set higher than that of any previous observed
        proposal id. Otherwise the previously used proposal id will simply be
        retransmitted.
        '''
        if increment_proposal_number:
            self.leader        = False
            self.promises_rcvd = set()
            self.proposal_id   = (self.next_proposal_number, self.proposer_uid)
        
            self.next_proposal_number += 1

        if self.active:
            self.messenger.send_prepare(self.proposal_id)

    
    def observe_proposal(self, from_uid, proposal_id):
        '''
        Optional method used to update the proposal counter as proposals are
        seen on the network.  When co-located with Acceptors and/or Learners,
        this method may be used to avoid a message delay when attempting to
        assume leadership (guaranteed NACK if the proposal number is too low).
        '''
        if from_uid != self.proposer_uid:
            if proposal_id >= (self.next_proposal_number, self.proposer_uid):
                self.next_proposal_number = proposal_id.number + 1

            
    def recv_prepare_nack(self, from_uid, proposal_id, promised_id):
        '''
        Called when an explicit NACK is sent in response to a prepare message.
        '''
        self.observe_proposal( from_uid, promised_id )

    
    def recv_accept_nack(self, from_uid, proposal_id, promised_id):
        '''
        Called when an explicit NACK is sent in response to an accept message
        '''

        
    def resend_accept(self):
        '''
        Retransmits an Accept! message iff this node is the leader and has
        a proposal value
        '''
        if self.leader and self.proposed_value and self.active:
            self.messenger.send_accept(self.proposal_id, self.proposed_value)


    def recv_promise(self, from_uid, proposal_id, prev_accepted_id, prev_accepted_value):
        '''
        Called when a Promise message is received from the network
        '''
        self.observe_proposal( from_uid, proposal_id )

        if self.leader or proposal_id != self.proposal_id or from_uid in self.promises_rcvd:
            return

        self.promises_rcvd.add( from_uid )
        
        if prev_accepted_id > self.last_accepted_id:
            self.last_accepted_id = prev_accepted_id
            # If the Acceptor has already accepted a value, we MUST set our proposal
            # to that value. Otherwise, we may retain our current value.
            if prev_accepted_value is not None:
                self.proposed_value = prev_accepted_value

        if len(self.promises_rcvd) == self.quorum_size:
            self.leader = True

            self.messenger.on_leadership_acquired()
            
            if self.proposed_value is not None and self.active:
                self.messenger.send_accept(self.proposal_id, self.proposed_value)


                
class Acceptor(object):

    messenger      = None    
    promised_id    = None
    accepted_id    = None
    accepted_value = None

    pending_promise  = None # None or the UID to send a promise message to
    pending_accepted = None # None or the UID to send an accepted message to
    active           = True
    
    
    @property
    def persistance_required(self):
        return self.pending_promise is not None or self.pending_accepted is not None


    def recover(self, promised_id, accepted_id, accepted_value):
        self.promised_id    = promised_id
        self.accepted_id    = accepted_id
        self.accepted_value = accepted_value
    

    def recv_prepare(self, from_uid, proposal_id):
        '''
        Called when a Prepare message is received from the network
        '''
        if proposal_id == self.promised_id:
            # Duplicate prepare message. No change in state is necessary so the response
            # may be sent immediately
            if self.active:
                self.messenger.send_promise(from_uid, proposal_id, self.accepted_id, self.accepted_value)
        
        elif proposal_id > self.promised_id:
            if self.pending_promise is None:
                self.promised_id = proposal_id
                if self.active:
                    self.pending_promise = from_uid

        else:
            if self.active:
                self.messenger.send_prepare_nack(from_uid, proposal_id, self.promised_id)

                    
    def recv_accept_request(self, from_uid, proposal_id, value):
        '''
        Called when an Accept! message is received from the network
        '''
        if proposal_id == self.accepted_id and value == self.accepted_value:
            # Duplicate accepted proposal. No change in state is necessary so the response
            # may be sent immediately
            if self.active:
                self.messenger.send_accepted(proposal_id, value)
            
        elif proposal_id >= self.promised_id:
            if self.pending_accepted is None:
                self.promised_id      = proposal_id
                self.accepted_value   = value
                self.accepted_id      = proposal_id
                if self.active:
                    self.pending_accepted = from_uid
            
        else:
            if self.active:
                self.messenger.send_accept_nack(from_uid, proposal_id, self.promised_id)


    def persisted(self):
        '''
        This method sends any pending Promise and/or Accepted messages. Prior to
        calling this method, the application must ensure that the promised_id
        accepted_id, and accepted_value variables have been persisted to stable
        media.
        '''
        if self.active:
            
            if self.pending_promise:
                self.messenger.send_promise(self.pending_promise,
                                            self.promised_id,
                                            self.accepted_id,
                                            self.accepted_value)
                
            if self.pending_accepted:
                self.messenger.send_accepted(self.accepted_id,
                                             self.accepted_value)
                
        self.pending_promise  = None
        self.pending_accepted = None


        
class Learner(object):

    quorum_size       = None

    proposals         = None # maps proposal_id => [accept_count, retain_count, value]
    acceptors         = None # maps from_uid => last_accepted_proposal_id
    final_value       = None
    final_proposal_id = None

    final_acceptors = None

    @property
    def complete(self):
        return self.final_proposal_id is not None
    
    def recv_accepted(self, from_uid, proposal_id, accepted_value):
        '''
        Called when an Accepted message is received from an acceptor
        '''
        if self.final_value is not None:
            if accepted_value == self.final_value:
                self.final_acceptors.add( from_uid )
            return # already done
            
        if self.proposals is None:
            self.proposals = dict()
            self.acceptors = dict()
            
        last_pn = self.acceptors.get(from_uid)

        if not proposal_id > last_pn:
            return # Old message

        self.acceptors[ from_uid ] = proposal_id
        
        if last_pn is not None:
            oldp = self.proposals[ last_pn ]
            oldp[1].remove( from_uid )
            if len(oldp[1]) == 0:
                del self.proposals[ last_pn ]

        if not proposal_id in self.proposals:
            self.proposals[ proposal_id ] = [set(), set(), accepted_value]

        t = self.proposals[ proposal_id ]

        assert accepted_value == t[2], 'Value mismatch for single proposal!'
        
        t[0].add( from_uid )
        t[1].add( from_uid )

        if len(t[0]) == self.quorum_size:
            self.final_value       = accepted_value
            self.final_proposal_id = proposal_id
            self.final_acceptors   = t[0]
            self.proposals         = None
            self.acceptors         = None

            self.messenger.on_resolution( proposal_id, accepted_value )

            

    
class Node (Proposer, Acceptor, Learner):
    '''
    This class supports the common model where each node on a network preforms
    all three Paxos roles, Proposer, Acceptor, and Learner.
    '''

    def __init__(self, messenger, node_uid, quorum_size):
        self.messenger   = messenger
        self.node_uid    = node_uid
        self.quorum_size = quorum_size


    @property
    def proposer_uid(self):
        return self.node_uid
            

    def change_quorum_size(self, quorum_size):
        self.quorum_size = quorum_size

        
    def recv_prepare(self, from_uid, proposal_id):
        self.observe_proposal( from_uid, proposal_id )
        return super(Node,self).recv_prepare( from_uid, proposal_id )

