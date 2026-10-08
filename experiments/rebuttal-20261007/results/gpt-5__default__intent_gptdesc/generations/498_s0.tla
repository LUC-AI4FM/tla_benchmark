---- MODULE MultiInstanceConsensus ----
EXTENDS Naturals, FiniteSets

CONSTANTS VALUE, SLOTS

ASSUME VALUE # {} /\ SLOTS # {}

VARIABLES Proposed, Chosen

vars == <<Proposed, Chosen>>

Init ==
  /\ Proposed = {}
  /\ Chosen = [s \in SLOTS |-> {}]

Propose ==
  \E v \in VALUE \ Proposed:
    /\ Proposed' = Proposed \cup {v}
    /\ Chosen' = Chosen

ChooseSlot(s) ==
  \E v \in Proposed:
    /\ s \in SLOTS
    /\ Chosen[s] = {}
    /\ Chosen' = [Chosen EXCEPT ![s] = {v}]
    /\ Proposed' = Proposed

Next ==
  Propose \/ (\E s \in SLOTS: ChooseSlot(s))

Fairness ==
  /\ WF_vars(Propose)
  /\ \A s \in SLOTS: WF_vars(ChooseSlot(s))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Safety and type invariants
*)
TypeOK ==
  /\ Proposed \subseteq VALUE
  /\ Chosen \in [SLOTS -> SUBSET VALUE]
  /\ \A s \in SLOTS: IsFiniteSet(Chosen[s])

NoMultiChoice ==
  \A s \in SLOTS: Cardinality(Chosen[s]) <= 1

ChosenFromProposed ==
  \A s \in SLOTS: Chosen[s] \subseteq Proposed

SafetyInv ==
  TypeOK /\ NoMultiChoice /\ ChosenFromProposed

(*
  Persistence (decisions are final)
*)
Persistence ==
  \A s \in SLOTS:
    \A v \in VALUE:
      [] (Chosen[s] = {v} => [] (Chosen[s] = {v}))

(*
  Liveness: every slot eventually acquires a chosen value
*)
EventualDecision ==
  \A s \in SLOTS: <> (\E v \in VALUE: Chosen[s] = {v})

====