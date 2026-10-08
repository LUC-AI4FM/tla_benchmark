------------------------------ MODULE LiveSpec ------------------------------
EXTENDS Naturals

CONSTANTS Candidates

VARIABLE Chosen

(* --- Initialization: nothing chosen yet --- *)
Init == Chosen = {}

(* --- Action: choose a value if none has been chosen before --- *)
Choose(v) ==
  /\ Chosen = {}
  /\ v \in Candidates
  /\ Chosen' = {v}

Next == Choose(v) \/ UNCHANGED Chosen

(* --- Safety specification (no fairness constraints) --- *)
SafetySpec == Init /\ [][Next]_Chosen

(* --- Safety invariant: chosen set is a subset of the candidates and contains at most one element --- *)
SafetyInvariant ==
  Chosen \subseteq Candidates
  /\ #Chosen <= 1

(* --- Liveness variant: weak fairness on the choice action --- *)
ChoiceAction == \E v \in Candidates : Choose(v)
LivenessProperty == WF_vars(ChoiceAction)

(* --- Final specification combining safety and liveness --- *)
Spec == SafetySpec /\ LivenessProperty

=============================================================================