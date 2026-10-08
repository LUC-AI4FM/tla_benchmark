MODULE TwoStateProcess
EXTENDS Naturals, Sequences

CONSTANTS MaxHistLen

VARIABLES pc, history

(* Control states *)
A == "A"
B == "B"

Init ==
  /\ pc = A
  /\ history = << >>

ActionA ==
  /\ pc = A
  /\ pc' = B
  /\ history' = Append(history, A)

ActionB ==
  /\ pc = B
  /\ pc' = A
  /\ history' = history

Next == ActionA \/ ActionB

SafetyInvariant == Len(history) <= MaxHistLen

LivenessProperty == <> (pc = "Done")

Spec ==
  Init
  /\ [] [Next]_vars
  /\ WF_Enabled(ActionA \/ ActionB)
  /\ SafetyInvariant

END MODULE