---- MODULE MultiInstanceConsensus ----
EXTENDS FiniteSets

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == << proposed, chosen >>

Init ==
  /\ proposed = {}
  /\ chosen = [ s \in Slots |-> {} ]

Propose ==
  \E v \in Values \ proposed:
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose ==
  \E s \in Slots, v \in proposed:
    /\ chosen[s] = {}
    /\ chosen' = [ chosen EXCEPT ![s] = {v} ]
    /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Propose) /\ WF_vars(Choose)

TypeOK ==
  /\ proposed \subseteq Values
  /\ chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots: IsFiniteSet(chosen[s])

Nontriviality ==
  \A s \in Slots: chosen[s] \subseteq proposed

Consistency ==
  \A s \in Slots: chosen[s] = {} \/ (\E v \in Values: chosen[s] = {v})

StableStep ==
  \A s \in Slots: chosen[s] # {} => chosen'[s] = chosen[s]

Stability ==
  [] [StableStep]_vars

Liveness ==
  \A s \in Slots: <> (chosen[s] # {})

====