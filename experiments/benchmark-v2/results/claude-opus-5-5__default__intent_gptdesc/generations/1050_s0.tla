------------------------------- MODULE EchoFlooding -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,      \* finite set of distinct node identities
    Edges,      \* set of ordered pairs <<p, q>> representing undirected edges
    None        \* a value that is not a node identity

ASSUME NodesFinite     == IsFiniteSet(Nodes) /\ Nodes # {}
ASSUME NoneNotNode     == None \notin Nodes
ASSUME EdgesWellTyped  == Edges \subseteq (Nodes \X Nodes)
ASSUME NoSelfLoops     == \A n \in Nodes : <<n, n>> \notin Edges
ASSUME Symmetric       == \A p, q \in Nodes : <<p, q>> \in Edges => <<q, p>> \in Edges

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges }

RECURSIVE ReachFrom(_, _)
ReachFrom(S, k) ==
    IF k = 0 THEN S
    ELSE ReachFrom(S \cup { m \in Nodes : \E n \in S : m \in Nbrs(n) }, k - 1)

ASSUME Connected == \A n \in Nodes : ReachFrom({n}, Cardinality(Nodes)) = Nodes

Msgs == [from : Nodes, id : Nodes]

VARIABLES
    initiator,  \* the node elected as initiator (None before election)
    believes,   \* believes[n]: identity n believes is the initiator (or None)
    parent,     \* parent[n]: neighbor from which n first learned the identity
    mailbox,    \* mailbox[n]: set of messages in transit to n (unordered)
    forwarded,  \* forwarded[n]: n has already forwarded the identity
    rcvd,       \* rcvd[n]: neighbors from which n has received a message
    echoed,     \* echoed[n]: n has sent its echo back to its parent
    decided     \* decided[n]: the initiator has collected all echoes

vars == <<initiator, believes, parent, mailbox, forwarded, rcvd, echoed, decided>>

TypeOK ==
    /\ initiator \in Nodes \cup {None}
    /\ believes  \in [Nodes -> Nodes \cup {None}]
    /\ parent    \in [Nodes -> Nodes \cup {None}]
    /\ mailbox   \in [Nodes -> SUBSET Msgs]
    /\ forwarded \in [Nodes -> BOOLEAN]
    /\ rcvd      \in [Nodes -> SUBSET Nodes]
    /\ echoed    \in [Nodes -> BOOLEAN]
    /\ decided   \in [Nodes -> BOOLEAN]

\* Send message from n carrying identity v to every node in targets.
\* Mailboxes are sets, so resending an identical message is idempotent.
SendTo(n, v, targets) ==
    [m \in Nodes |-> IF m \in targets
                       THEN mailbox[m] \cup {[from |-> n, id |-> v]}
                       ELSE mailbox[m]]

Init ==
    /\ initiator = None
    /\ believes  = [n \in Nodes |-> None]
    /\ parent    = [n \in Nodes |-> None]
    /\ mailbox   = [n \in Nodes |-> {}]
    /\ forwarded = [n \in Nodes |-> FALSE]
    /\ rcvd      = [n \in Nodes |-> {}]
    /\ echoed    = [n \in Nodes |-> FALSE]
    /\ decided   = [n \in Nodes |-> FALSE]

\* Any node may nondeterministically become the (single) initiator.
Initiate(n) ==
    /\ initiator = None
    /\ initiator' = n
    /\ believes'  = [believes EXCEPT ![n] = n]
    /\ forwarded' = [forwarded EXCEPT ![n] = TRUE]
    /\ mailbox'   = SendTo(n, n, Nbrs(n))
    /\ UNCHANGED <<parent, rcvd, echoed, decided>>

\* Delivery of a message to n (arbitrary order, arbitrary delay).
Receive(n, msg) ==
    /\ msg \in mailbox[n]
    /\ mailbox' = [mailbox EXCEPT ![n] = @ \ {msg}]
    /\ rcvd'    = [rcvd EXCEPT ![n] = @ \cup {msg.from}]
    /\ IF believes[n] = None
         THEN /\ believes' = [believes EXCEPT ![n] = msg.id]
              /\ parent'   = [parent EXCEPT ![n] = msg.from]
         ELSE UNCHANGED <<believes, parent>>
    /\ UNCHANGED <<initiator, forwarded, echoed, decided>>

\* A non-initiator forwards the adopted identity to all neighbors but its parent.
Forward(n) ==
    /\ believes[n] # None
    /\ n # initiator
    /\ ~forwarded[n]
    /\ forwarded' = [forwarded EXCEPT ![n] = TRUE]
    /\ mailbox'   = SendTo(n, believes[n], Nbrs(n) \ {parent[n]})
    /\ UNCHANGED <<initiator, believes, parent, rcvd, echoed, decided>>

\* Once a non-initiator has heard from all neighbors, it echoes to its parent.
Echo(n) ==
    /\ n # initiator
    /\ forwarded[n]
    /\ ~echoed[n]
    /\ rcvd[n] = Nbrs(n)
    /\ echoed'  = [echoed EXCEPT ![n] = TRUE]
    /\ mailbox' = SendTo(n, believes[n], {parent[n]})
    /\ UNCHANGED <<initiator, believes, parent, forwarded, rcvd, decided>>

\* The initiator decides once it has heard back from all neighbors.
Decide(n) ==
    /\ n = initiator
    /\ ~decided[n]
    /\ rcvd[n] = Nbrs(n)
    /\ decided' = [decided EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<initiator, believes, parent, mailbox, forwarded, rcvd, echoed>>

Next ==
    \/ \E n \in Nodes : Initiate(n)
    \/ \E n \in Nodes : \E msg \in Msgs : Receive(n, msg)
    \/ \E n \in Nodes : Forward(n)
    \/ \E n \in Nodes : Echo(n)
    \/ \E n \in Nodes : Decide(n)

Fairness ==
    /\ WF_vars(\E n \in Nodes : Initiate(n))
    /\ \A n \in Nodes : \A msg \in Msgs : WF_vars(Receive(n, msg))
    /\ \A n \in Nodes : WF_vars(Forward(n))
    /\ \A n \in Nodes : WF_vars(Echo(n))
    /\ \A n \in Nodes : WF_vars(Decide(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------
\* Safety properties

\* No node ever believes an identity other than the actual initiator.
AgreementInv ==
    \A n \in Nodes : believes[n] \in {None, initiator}

\* Every message in transit carries the initiator's identity.
MsgsCarryInitiator ==
    \A n \in Nodes : \A msg \in mailbox[n] :
        /\ msg.id = initiator
        /\ msg.from \in Nbrs(n)

\* A node that has forwarded has adopted the identity it forwarded (the initiator).
ForwardConsistent ==
    \A n \in Nodes : forwarded[n] => (believes[n] # None /\ believes[n] = initiator)

\* Echoes only go up after forwarding; decisions only by the initiator.
EchoConsistent ==
    \A n \in Nodes :
        /\ echoed[n] => forwarded[n]
        /\ decided[n] => n = initiator

SafetyInv ==
    /\ TypeOK
    /\ AgreementInv
    /\ MsgsCarryInitiator
    /\ ForwardConsistent
    /\ EchoConsistent

\* Once an initiator is elected it never changes.
InitiatorStable ==
    [][initiator # None => initiator' = initiator]_vars

\* Once a node adopts an identity it never changes it.
BeliefStable ==
    [][\A n \in Nodes : believes[n] # None => believes'[n] = believes[n]]_vars

\* Once a node has forwarded, it stays forwarded and never forwards a different id.
ForwardMonotone ==
    [][\A n \in Nodes :
         forwarded[n] => (forwarded'[n] /\ believes'[n] = believes[n])]_vars

\* Eventually no node believes an identity other than the actual initiator.
EventualAgreement ==
    <>[](initiator # None /\ \A n \in Nodes : believes[n] \in {None, initiator})

-----------------------------------------------------------------------------------
\* Liveness properties

AllAdopted ==
    initiator # None /\ \A n \in Nodes : believes[n] = initiator

NoMsgsInTransit ==
    \A n \in Nodes : mailbox[n] = {}

Terminated ==
    /\ AllAdopted
    /\ NoMsgsInTransit
    /\ decided[initiator]

\* Every node eventually adopts the initiator identity.
EventuallyAllAdopt == <>[]AllAdopted

\* Flooding terminates: all nodes adopt, no messages remain, initiator decides.
Termination == <>[]Terminated

\* The initiator decides only after every node has adopted its identity.
DecideImpliesAll ==
    [](\A n \in Nodes : decided[n] => AllAdopted)

=============================================================================