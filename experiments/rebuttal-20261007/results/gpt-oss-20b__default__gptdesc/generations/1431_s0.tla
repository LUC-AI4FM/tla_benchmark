MODULE TwoStateProcess
EXTENDS Naturals, Sequences

CONSTANT MAXLEN \in Nat

VARIABLES pc, hist

(* Initial state *)
Init ==
    /\ pc = "A"
    /\ hist = <<>>

(* Action A: from A to B, append current control state to history *)
ActionA ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ hist' = Append(hist, "A")

(* Action B: from B to A, leave history unchanged *)
ActionB ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ hist' = hist

Next == ActionA \/ ActionB

SafetyInvariant == Len(hist) <= MAXLEN
LivenessProperty == <> (pc = "Done")

Spec == Init /\ [][Next]_<<pc, hist>> /\ WF_0(Next)