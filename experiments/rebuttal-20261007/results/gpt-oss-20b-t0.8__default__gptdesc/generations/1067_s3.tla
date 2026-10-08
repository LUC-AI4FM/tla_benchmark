MODULE RingTermination
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node

VARIABLES Active, Detected

Active \in SUBSET Node
Detected \in BOOLEAN

vars == <<Active, Detected>>

Init ==
  /\ Active ⊆ Node
  /\ Detected = FALSE

Terminate(i) ==
  /\ i \in Active
  /\ Active' = Active \ {i}
  /\ Detected' = Detected

WakeUp(i,j) ==
  /\ i \in Active
  /\ j \in Node \ Active
  /\ Active' = Active ∪ {j}
  /\ Detected' = Detected

Detect ==
  /\ Active = {}
  /\ ~Detected
  /\ Detected' = TRUE
  /\ Active' = Active

Next ==
  \/ ∃i \in Active : Terminate(i)
  \/ ∃i \in Active, j \in Node \ Active : WakeUp(i,j)
  \/ Detect

InvariantActiveSubset == Active ⊆ Node
InvariantDetectedImplyEmpty == Detected => Active = {}

Correctness == [] (Detected <=> Active = {})

Quiescence == <> (Active = {} /\ Detected)

Spec == Init /\ [][Next]_vars /\ WF_actions(Detect)