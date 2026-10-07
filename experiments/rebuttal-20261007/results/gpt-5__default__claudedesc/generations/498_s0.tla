----------------------------- MODULE MultiInstanceConsensus -----------------------------
EXTENDS FiniteSets

CONSTANTS Values, Slots

ASSUME /\ Values # {}
        /\ Slots # {}

VARIABLES proposed, chosen

vars == << proposed, chosen >>

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
  /\ v \in Values \ proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED chosen

Choose(s, v) ==
  /\ s \in Slots
  /\ v \in proposed
  /\ chosen[s] = {}
  /\ chosen' = [chosen EXCEPT ![s] = {v}]
  /\ UNCHANGED proposed

Next ==
  (\E v \in Values: Propose(v))
  \/ (\E s \in Slots: \E v \in Values: Choose(s, v))

Spec ==
  Init /\ [][Next]_vars

LiveSpec ==
  Spec
  /\ (\A v \in Values: WF_vars(Propose(v)))
  /\ (\A s \in Slots: \A v \in Values: WF_vars(Choose(s, v)))

TypeOK ==
  /\ proposed \subseteq Values
  /\ chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots: IsFiniteSet(chosen[s])

Nontriviality ==
  \A s \in Slots: chosen[s] \subseteq proposed

Consistency ==
  \A s \in Slots: (chosen[s] = {}) \/ (\E v \in Values: chosen[s] = {v})

Stability ==
  \A s \in Slots: \A v \in Values: [] (chosen[s] = {v} => [] (chosen[s] = {v}))

Liveness ==
  \A s \in Slots: <> (chosen[s] # {})

=============================================================================