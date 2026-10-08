MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANTS N, MaxTicket

VARIABLES choosing, number, inCS

TypeOK ==
    /\ choosing \in [1..N -> BOOLEAN]
    /\ number   \in [1..N -> Nat]
    /\ inCS     \in [1..N -> BOOLEAN]

Init ==
    /\ choosing = [i \in 1..N |-> FALSE]
    /\ number   = [i \in 1..N |-> 0]
    /\ inCS     = [i \in 1..N |-> FALSE]
    /\ TypeOK

SetChoosingTrue(p) ==
    /\ p \in 1..N
    /\ NOT choosing[p]
    /\ number[p] = 0
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<number, inCS>>

SetNumberAndFalse(p) ==
    /\ p \in 1..N
    /\ choosing[p]
    /\ number[p] = 0
    /\ LET maxNum == Max( { number[q] : q \in 1..N } ) IN
       /\ number'   = [number EXCEPT ![p] = maxNum + 1]
       /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ UNCHANGED inCS

EnterCS(p) ==
    /\ p \in 1..N
    /\ number[p] > 0
    /\ NOT choosing[p]
    /\ \A q \in 1..N :
          (q = p \/ (number[q] = 0 \/ ((number[q], q) > (number[p], p))))
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<choosing, number>>

ExitCS(p) ==
    /\ p \in 1..N
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ number' = [number EXCEPT ![p] = 0]
    /\ UNCHANGED choosing

Next == 
    \E p \in 1..N :
        SetChoosingTrue(p) \/ SetNumberAndFalse(p) \/ EnterCS(p) \/ ExitCS(p)

MutualExclusion ==
    \A i, j \in 1..N : (i < j) => ~(inCS[i] /\ inCS[j])

Spec == Init /\ [][Next]_<<choosing, number, inCS>> /\ MutualExclusion