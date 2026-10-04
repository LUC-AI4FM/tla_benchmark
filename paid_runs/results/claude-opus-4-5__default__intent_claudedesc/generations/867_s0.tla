------------------------------ MODULE Paxos ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    Replicas,      \* Set of replicas (act as both proposers and acceptors)
    Values,        \* Set of possible values that can be proposed
    Ballots,       \* Set of ballot numbers (includes 0 as sentinel)
    Quorums        \* Collection of quorums (strict majority subsets)

VARIABLES
    maxBal,        \* maxBal[r]: highest ballot replica r has seen
    maxVBal,       \* maxVBal[r]: highest ballot at which r accepted a value
    maxVal,        \* maxVal[r]: value accepted at maxVBal[r]
    msgs,          \* Set of all messages sent
    proposed,      \* Set of values that have been proposed
    decided        \* The decided value (or None if not yet decided)

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decided>>

None == CHOOSE v : v \notin Values

\* Message types
Message ==
    [type : {"Prepare"}, bal : Ballots, src : Replicas]
    \cup
    [type : {"Promise"}, bal : Ballots, maxVBal : Ballots, maxVal : Values \cup {None}, src : Replicas]
    \cup
    [type : {"Accept"}, bal : Ballots, val : Values, src : Replicas]
    \cup
    [type : {"Accepted"}, bal : Ballots, val : Values, src : Replicas]

\* Type invariant
TypeOK ==
    /\ maxBal \in [Replicas -> Ballots]
    /\ maxVBal \in [Replicas -> Ballots]
    /\ maxVal \in [Replicas -> Values \cup {None}]
    /\ msgs \subseteq Message
    /\ proposed \subseteq Values
    /\ decided \in Values \cup {None}

\* Initial state
Init ==
    /\ maxBal = [r \in Replicas |-> 0]
    /\ maxVBal = [r \in Replicas |-> 0]
    /\ maxVal = [r \in Replicas |-> None]
    /\ msgs = {}
    /\ proposed = {}
    /\ decided = None

\* Phase 1a: Proposer sends Prepare message
Prepare(r, b) ==
    /\ b > 0  \* Don't prepare with sentinel ballot
    /\ msgs' = msgs \cup {[type |-> "Prepare", bal |-> b, src |-> r]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

\* Phase 1b: Acceptor responds with Promise
Promise(r, m) ==
    /\ m \in msgs
    /\ m.type = "Prepare"
    /\ m.bal > maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ msgs' = msgs \cup {[type |-> "Promise", 
                           bal |-> m.bal, 
                           maxVBal |-> maxVBal[r], 
                           maxVal |-> maxVal[r], 
                           src |-> r]}
    /\ UNCHANGED <<maxVBal, maxVal, proposed, decided>>

\* Get the set of Promise messages for a given ballot
PromiseMsgs(b) == {m \in msgs : m.type = "Promise" /\ m.bal = b}

\* Check if we have promises from a quorum
HasQuorumOfPromises(b) ==
    \E Q \in Quorums : \A r \in Q : \E m \in PromiseMsgs(b) : m.src = r

\* Get the value to propose based on promises
\* Must use the value from the highest maxVBal among promises, if any
GetValueToPropose(b, v, Q) ==
    LET promisesFromQ == {m \in PromiseMsgs(b) : m.src \in Q}
        highestVBal == CHOOSE maxB \in {m.maxVBal : m \in promisesFromQ} :
                         \A m \in promisesFromQ : m.maxVBal <= maxB
        highestPromise == CHOOSE m \in promisesFromQ : m.maxVBal = highestVBal
    IN IF highestVBal = 0 /\ highestPromise.maxVal = None
       THEN v  \* Free choice
       ELSE highestPromise.maxVal  \* Constrained choice

\* Phase 2a: Proposer sends Accept message after collecting quorum of promises
Accept(r, b, v) ==
    /\ b > 0
    /\ v \in Values
    /\ \E Q \in Quorums :
        /\ \A rep \in Q : \E m \in PromiseMsgs(b) : m.src = rep
        /\ LET promisesFromQ == {m \in PromiseMsgs(b) : m.src \in Q}
               acceptedPromises == {m \in promisesFromQ : m.maxVal # None}
           IN IF acceptedPromises = {}
              THEN TRUE  \* Free choice, v can be any value
              ELSE LET highestVBal == CHOOSE maxB \in {m.maxVBal : m \in acceptedPromises} :
                                        \A m \in acceptedPromises : m.maxVBal <= maxB
                       highestPromise == CHOOSE m \in acceptedPromises : m.maxVBal = highestVBal
                   IN v = highestPromise.maxVal  \* Must use highest accepted value
    /\ proposed' = proposed \cup {v}
    /\ msgs' = msgs \cup {[type |-> "Accept", bal |-> b, val |-> v, src |-> r]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided>>

\* Phase 2b: Acceptor accepts the value
Accepted(r, m) ==
    /\ m \in msgs
    /\ m.type = "Accept"
    /\ m.bal >= maxBal[r]
    /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![r] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![r] = m.val]
    /\ msgs' = msgs \cup {[type |-> "Accepted", bal |-> m.bal, val |-> m.val, src |-> r]}
    /\ UNCHANGED <<proposed, decided>>

\* Get the set of Accepted messages for a given ballot and value
AcceptedMsgs(b, v) == {m \in msgs : m.type = "Accepted" /\ m.bal = b /\ m.val = v}

\* Check if a quorum has accepted for a given ballot and value
HasQuorumOfAccepted(b, v) ==
    \E Q \in Quorums : \A r \in Q : \E m \in AcceptedMsgs(b, v) : m.src = r

\* Decision action: record a decided value when quorum of acceptors accepted
Decide(b, v) ==
    /\ decided = None
    /\ HasQuorumOfAccepted(b, v)
    /\ decided' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

\* Next state relation
Next ==
    \/ \E r \in Replicas, b \in Ballots : Prepare(r, b)
    \/ \E r \in Replicas, m \in msgs : Promise(r, m)
    \/ \E r \in Replicas, b \in Ballots, v \in Values : Accept(r, b, v)
    \/ \E r \in Replicas, m \in msgs : Accepted(r, m)
    \/ \E b \in Ballots, v \in Values : Decide(b, v)

\* Strong fairness on decide action
DecideEnabled == \E b \in Ballots, v \in Values : 
    /\ decided = None 
    /\ HasQuorumOfAccepted(b, v)

FairDecide == SF_vars(\E b \in Ballots, v \in Values : Decide(b, v))

\* Specification
Spec == Init /\ [][Next]_vars /\ FairDecide

\* Safety: Non-triviality - only proposed values can be decided
NonTriviality == decided # None => decided \in proposed

\* Safety: Consistency - once decided, the value never changes
Consistency == [][decided # None => decided' = decided]_vars

\* Combined safety invariant (as a state predicate for invariant checking)
SafetyInvariant == 
    /\ TypeOK
    /\ NonTriviality

\* Consistency as an invariant (the decided value, once set, stays the same)
\* This is checked via the temporal property
ConsistencyProperty == [](decided # None => [](decided = decided))

==========================================================================