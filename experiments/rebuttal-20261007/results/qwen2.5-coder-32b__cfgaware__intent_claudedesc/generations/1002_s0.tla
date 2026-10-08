------------------------------- MODULE BarrierSync -------------------------------

CONSTANTS N \* Number of processes

VARIABLES arrivals, phase

\* Process states
CONSTANT Arrived, Waiting

\* Initial predicate
Init == /\ arrivals = {}
        /\ phase = [p \in 1..N -> Waiting]

\* Next-state relation
Next ==
    \/ \E p \in 1..N :
        /\ phase[p] = Waiting
        /\ arrivals' = arrivals \cup {p}
        /\ phase' = [phase EXCEPT ![p] = Arrived]
    \/ /\ arrivals = {1..N}
       /\ phase' = [p \in 1..N -> Waiting]
       /\ arrivals' = {}

\* Specification
Spec == Init /\ [][Next]_<<arrivals, phase>>

\* Type invariant: each process is in one of the two valid states
TypeOK ==
    /\ arrivals \subseteq (1..N)
    /\ \A p \in 1..N : phase[p] \in {Arrived, Waiting}

\* Barrier property: no premature releases occur
BarrierProperty ==
    [](arrivals = {1..N} => <>(phase' = [p \in 1..N -> Waiting]))

=============================================================================