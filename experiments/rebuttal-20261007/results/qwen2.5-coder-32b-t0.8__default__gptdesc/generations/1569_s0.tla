------------------------------- MODULE Bakery -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES choosing, number, nextProc, maxima, readSet, pc

vars == <<choosing, number, nextProc, maxima, readSet, pc>>

Init == 
    /\ choosing = [p \in 1..N -> FALSE]
    /\ number   = [p \in 1..N -> 0]
    /\ nextProc = [p \in 1..N -> 1]
    /\ maxima   = [p \in 1..N -> 0]
    /\ readSet  = [p \in 1..N -> {}]
    /\ pc      = [p \in 1..N -> "entry"]

Next == 
    \E p \in 1..N : \/ /\ pc[p] = "entry"
                           /\ ~choosing[p]
                           /\ nextProc[p] \notin (1..N) \ {p}
                           /\ readSet[p] = {}
                           /\ maxima[p] = _max
                           /\ number[p] = maxima[p] + 1
                           /\ choosing[p]
                           /\ pc'[p] = "choosing"
                  \/ /\ pc[p] = "choosing"
                           /\ \A q \in (1..N) \ {p} : 
                               \/ ~choosing[q]
                               \/ number[q] < number[p]
                               \/ number[q] = number[p] /\ q < p
                           /\ pc'[p] = "critical_section"
                  \/ /\ pc[p] = "critical_section"
                           /\ pc'[p] = "release"
                  \/ /\ pc[p] = "release"
                           /\ nextProc[p] \in (1..N) \ {p}
                           /\ readSet[p] = {}
                           /\ maxima[p] = _max
                           /\ number[p]' = 0
                           /\ choosing[p]' = FALSE
                           /\ pc'[p] = "entry"

Spec == Init /\ [][Next]_<<vars>>

\_max ==
    LET allNumbers == {number[q] : q \in (1..N) \ {p} \cup {number[p]}}
    IN CHOOSE max \in allNumbers : \A n \in allNumbers : n \leq max

InvariantMutualExclusion == 
    \A p, q \in 1..N :
        /\ pc[p] = "critical_section"
        /\ pc[q] = "critical_section"
        => p = q

StateConstraintTicketValues ==
    \A p \in 1..N : number[p] \in 0..(N * N)

Inv == InvariantMutualExclusion /\ StateConstraintTicketValues

SpecWithInvariants == Spec /\ Inv
============================================================