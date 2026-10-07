------------------------------- MODULE MultiSlotConsensus -------------------------------

EXTENDS Naturals

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == << proposed, chosen >>

Init ==
  /\ proposed = {}
  /\ chosen = [ s \in Slots |-> {} ]

Propose ==
  \E v \in Values \ proposed:
    /\ proposed' = proposed \cup {v}
    /\ chosen' = chosen

Choose ==
  \E s \in Slots:
    /\ chosen[s] = {}
    /\ \E v \in proposed:
        /\ proposed' = proposed
        /\ chosen' = [ chosen EXCEPT ![s] = {v} ]

Next == Propose \/ Choose

TypeOK ==
  /\ proposed \subseteq Values
  /\ chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots: chosen[s] = {} \/ \E v \in Values: chosen[s] = {v}

Nontrivial ==
  \A s \in Slots: chosen[s] \subseteq proposed

PerSlotConsistency ==
  \A s \in Slots:
    \A u, v \in Values:
      chosen[s] = {u} /\ chosen[s] = {v} => u = v

SafetyInv == TypeOK /\ Nontrivial /\ PerSlotConsistency

Stability ==
  \A s \in Slots:
    \A v \in Values:
      [] (chosen[s] = {v} => [] (chosen[s] = {v}))

EventuallyAllSlotsNonEmpty ==
  <> (\A s \in Slots: chosen[s] # {})

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => []SafetyInv

THEOREM Spec => Stability

THEOREM Spec => EventuallyAllSlotsNonEmpty

========================================================================================