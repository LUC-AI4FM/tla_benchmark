------------------------------- MODULE HuangAlgorithm -------------------------------

CONSTANTS 
    Procs,          \* Set of all processes
    Leader          \* Designated leader process

VARIABLES 
    weights,        \* Local weight held by each process
    inTransit,      \* Weight in transit from one process to another
    activeProcs     \* Set of currently active processes

ASSUME Procs \subseteq Nat /\ Cardinality(Procs) >= 1
ASSUME Leader \in Procs

CONSTANT MaxDenominator \* Bound for weight fractions to prevent Zeno behaviors

Init == 
    /\ weights = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ inTransit = {}
    /\ activeProcs = {Leader}

Next ==
    \/ \E p \in activeProcs, q \in (Procs \ {p}) :
        /\ q \notin activeProcs
        /\ weights' = [weights EXCEPT ![q] = weights[q] + weights[p]]
        /\ inTransit' = inTransit \cup {(p, q, weights[p])}
        /\ weights'[p] = 0
        /\ activeProcs' = activeProcs \ {p}
    \/ \E p \in (Procs \ activeProcs) :
        /\ weights[p] > 0
        /\ weights' = [weights EXCEPT ![p] = 1]
        /\ inTransit' = inTransit
        /\ activeProcs' = activeProcs \cup {p}
    \/ \E p \in Procs, q \in (Procs \ {p}), w \in Nat :
        /\ <<p, q, w>> \in inTransit
        /\ weights' = [weights EXCEPT ![q] = weights[q] + w]
        /\ inTransit' = inTransit \ {<<p, q, w>>}
    \/ \E p \in activeProcs :
        /\ p /= Leader
        /\ weights[p] > 0
        /\ weights' = [weights EXCEPT ![p] = 1]
        /\ inTransit' = inTransit
        /\ activeProcs' = activeProcs

Spec == Init /\ [][Next]_<<activeProcs, weights, inTransit>>

Termination ==
    /\ Leader \notin activeProcs
    /\ weights[Leader] = 1
    /\ inTransit = {}

Safety ==
    G(Termination -> (\A p \in Procs : p \notin activeProcs) /\ inTransit = {})

Liveness ==
    [](G(\A p \in Procs : p \notin activeProcs) /\ inTransit = {}) -> F Termination

StateConstraint ==
    \A p \in Procs, q \in (Procs \ {p}), w \in Nat :
        <<p, q, w>> \in inTransit => w > 0 /\ w <= MaxDenominator
    /\ \A p \in Procs : weights[p] >= 0 /\ weights[p] <= 1

CompleteSpec ==
    Spec /\ StateConstraint /\ Safety /\ Liveness

=============================================================================