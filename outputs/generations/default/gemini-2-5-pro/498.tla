------------------------ MODULE MultiSlotConsensus ------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Value, Slot
ASSUME IsFiniteSet(Slot) /\ (Value # {})

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK == /\ proposed \subseteq Value
          /\ chosen \in [Slot -> SUBSET Value]

Init == /\ proposed = {}
        /\ chosen = [s \in Slot |-> {}]

Propose(v) == /\ v \in Value
              /\ v \notin proposed
              /\ proposed' = proposed \cup {v}
              /\ UNCHANGED chosen

Choose(s, v) == /\ s \in Slot
                /\ v \in proposed
                /\ chosen[s] = {}
                /\ chosen' = [chosen EXCEPT ![s] = {v}]
                /\ UNCHANGED proposed

Next == \/ (\E v \in Value : Propose(v))
        \/ (\E s \in Slot, v \in proposed : Choose(s,v))

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(Next)

\*===========================================================================