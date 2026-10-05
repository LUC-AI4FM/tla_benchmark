---------------------------- MODULE PaxosSpec ----------------------------

CONSTANTS 
    Replicas,       \* Set of replicas (acting as both proposers and acceptors)
    Values,         \* Set of possible values that can be proposed
    Ballots,        \* Set of ballot numbers (including 0 as sentinel)
    Quorums         \* Set of quorums (strict majority subsets of Replicas)

VARIABLES
    maxBal,         \* maxBal[a] = highest ballot acceptor a has seen
    maxVBal,        \* maxVBal[a] = highest ballot at which acceptor a accepted
    maxVal,         \* maxVal[a] = value accepted at maxVBal[a]
    msgs,           \* Set of all messages sent
    proposed,       \* Set of values that have been proposed
    decided         \* The decided value (or None if not yet decided)

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decided>>

None == CHOOSE v : v \notin Values

Messages ==
    [type : {"Prepare"}, bal : Ballots, src : Replicas]
    \cup
    [type : {"Promise"}, bal : Ballots, acc : Replicas, 
     maxVBal : Ballots, maxVal : Values \cup {None}]
    \cup
    [type : {"Accept"}, bal : Ballots, val : Values, src : Replicas]
    \cup
    [type : {"Accepted"}, bal : Ballots, val : Values, acc : Replicas]

PaxosTypeOK ==
    /\ maxBal \in [Replicas -> Ballots]
    /\ maxVBal \in [Replicas -> Ballots]
    /\ maxVal \in [Replicas -> Values \cup {None}]
    /\ msgs \subseteq Messages
    /\ proposed \subseteq Values
    /\ decided \in Values \cup {None}

Init ==
    /\ maxBal = [a \in Replicas |-> 0]
    /\ maxVBal = [a \in Replicas |-> 0]
    /\ maxVal = [a \in Replicas |-> None]
    /\ msgs = {}
    /\ proposed = {}
    /\ decided = None

-----------------------------------------------------------------------------
(* Phase 1a: Proposer sends Prepare message for ballot b *)
Prepare(p, b) ==
    /\ b > 0  \* Don't prepare with sentinel ballot
    /\ msgs' = msgs \cup {[type |-> "Prepare", bal |-> b, src |-> p]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

(* Phase 1b: Acceptor responds to Prepare with Promise *)
Promise(a, m) ==
    /\ m \in msgs
    /\ m.type = "Prepare"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ msgs' = msgs \cup {[type |-> "Promise", 
                           bal |-> m.bal, 
                           acc |-> a,
                           maxVBal |-> maxVBal[a],
                           maxVal |-> maxVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVal, proposed, decided>>

(* Phase 2a: Proposer sends Accept after receiving promises from a quorum *)
Accept(p, b, v) ==
    /\ b > 0
    /\ \E Q \in Quorums :
        LET promiseMsgs == {m \in msgs : m.type = "Promise" /\ m.bal = b /\ m.acc \in Q}
        IN
        /\ \A a \in Q : \E m \in promiseMsgs : m.acc = a
        /\ \/ /\ \A m \in promiseMsgs : m.maxVal = None
              /\ v \in Values
           \/ /\ \E m \in promiseMsgs : m.maxVal # None
              /\ \E m \in promiseMsgs :
                   /\ m.maxVal = v
                   /\ \A m2 \in promiseMsgs : m2.maxVBal <= m.maxVBal
    /\ proposed' = proposed \cup {v}
    /\ msgs' = msgs \cup {[type |-> "Accept", bal |-> b, val |-> v, src |-> p]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided>>

(* Phase 2b: Acceptor accepts the value if it hasn't promised higher *)
Accepted(a, m) ==
    /\ m \in msgs
    /\ m.type = "Accept"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ msgs' = msgs \cup {[type |-> "Accepted", 
                           bal |-> m.bal, 
                           val |-> m.val, 
                           acc |-> a]}
    /\ UNCHANGED <<proposed, decided>>

(* Decision: A value is decided when a quorum has accepted it for the same ballot *)
Decide ==
    /\ decided = None
    /\ \E b \in Ballots, v \in Values, Q \in Quorums :
        /\ b > 0
        /\ \A a \in Q : [type |-> "Accepted", bal |-> b, val |-> v, acc |-> a] \in msgs
        /\ decided' = v
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

-----------------------------------------------------------------------------
Next ==
    \/ \E p \in Replicas, b \in Ballots : Prepare(p, b)
    \/ \E a \in Replicas, m \in msgs : Promise(a, m)
    \/ \E p \in Replicas, b \in Ballots, v \in Values : Accept(p, b, v)
    \/ \E a \in Replicas, m \in msgs : Accepted(a, m)
    \/ Decide

Fairness == SF_vars(Decide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

(* Non-triviality: Only proposed values can be decided *)
PaxosNontriviality == decided # None => decided \in proposed

(* Consistency: Once decided, the value never changes *)
PaxosConsistency == [][decided # None => decided' = decided]_vars

=============================================================================