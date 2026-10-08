------------------------------- MODULE CounterSpec -------------------------------
EXTENDS Naturals

CONSTANTS MaxCount

VARIABLES count

Init == count = 0

Next ==
    \/ /\ count < MaxCount
       /\ count' = count + 1
    \/ /\ count = MaxCount
       /\ count' = count

Spec ==
    /\ Init
    /\ [][Next]_<<count>>
    /\ WF_[Next]_<<count>>

Termination == <>(count = MaxCount)

UniqueState5 == [](count = 5 => <>[](count = 5))

UniqueState9 == [](count = 9 => <>[](count = 9))

Invariant ==
    /\ count \in 0..MaxCount
    /\ UniqueState5
    /\ UniqueState9

THEOREM Spec => []Invariant

=============================================================================