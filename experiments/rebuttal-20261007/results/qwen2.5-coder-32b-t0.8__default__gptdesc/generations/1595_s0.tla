------------------------------- MODULE SequentialCounter -------------------------------

EXTENDS Naturals, FiniteSequences

CONSTANTS MaxCount

VARIABLES x, pc

Init == 
    /\ x = 0
    /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x < MaxCount
       /\ x' = x + 1
       /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ x < MaxCount
       /\ x' = x + 1
       /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ x >= MaxCount
       /\ x' = x
       /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc>> /\ WF_[Next]_<<pc>>

AtFive == x = 5

FinishLoop == pc = "Done"

PossibleCounts ==
    \E trace \in TLCGet("StateTrace"):
        LET states == { s.x : s \in trace }
        IN
            /\ Cardinality({s \in states: s = 0}) = 1
            /\ Cardinality({s \in states: s = MaxCount}) >= 1

=============================================================================