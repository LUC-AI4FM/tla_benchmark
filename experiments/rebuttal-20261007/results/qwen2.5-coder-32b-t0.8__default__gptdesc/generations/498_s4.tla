```tla
MODULE MultiSlotConsensus

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Slots  \* A finite set of slots
    Values \* A finite set of possible values

VARIABLES 
    proposedValues, \* Set of all values that have been proposed
    chosen          \* Mapping from slots to sets of values (each slot can only choose one value)

Init == /\ proposedValues = {}
        /\ chosen = [s \in Slots |-> {}]

Next ==
  \/ \E v \in Values \ (proposedValues):
      /\ proposedValues' = proposedValues \cup {v}
      /\ UNCHANGED chosen
  \/ \E s \in Slots, v \in proposedValues:
      /\ chosen[s] = {}
      /\ chosen' = [chosen EXCEPT ![s] = {v}]
      /\ UNCHANGED proposedValues

Spec == SpecForall(Init, Next)

\* Type correctness: proposedValues is a subset of Values
TypeOK ==
  proposedValues \subseteq Values

\* Nontriviality: at least one value has been proposed
Nontrivial ==
  proposedValues /= {}

\* Stability: if a slot has chosen a value, it does not change
Stability ==
  \A s \in Slots, v \in chosen[s]:
    \A v' \in chosen'[s]: v = v'

\* Per-slot consistency: each slot can only choose one value from proposedValues
PerSlotConsistency ==
  \A s \in Slots:
    \/ chosen[s] = {}
    \/ (\E v \in chosen[s]: v \in proposedValues)

Invariants ==
  /\ TypeOK
  /\ Nontrivial
  /\ Stability
  /\ PerSlotConsistency

\* Liveness: every slot eventually becomes nonempty
\[WF_vars\]_Next ==
  WF_vars(Next)

Liveness ==
  \A s \in Slots:
    <>(\E v \in Values: chosen[s] = {v})

SpecForall == Init /\ [][Next]_<<proposedValues, chosen>> /\ Invariants

THEOREM Spec => []Invariants

THEOREM Spec /\ WF_vars(Next) => Liveness
```