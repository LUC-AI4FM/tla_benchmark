MODULE TwoStateProcess

EXTENDS Naturals, Sequences, TLC

CONSTANT MaxHist

VARIABLES pc, hist

vars == <<pc, hist>>

Init ==
  /\ pc = "A"
  /\ hist = << >>

ActionA ==
  /\ pc' = "B"
  /\ hist' = Append(hist, pc)

ActionB ==
  /\ pc' = "A"
  /\ hist' = hist

Stutter ==
  /\ pc' = pc
  /\ hist' = hist

Next == ActionA \/ ActionB \/ Stutter

Safety == [] (Len(hist) <= MaxHist)

Liveness == <> (pc = "Done")

Spec == Init
       /\ [][Next]_vars
       /\ WF_vars(ActionA \/ ActionB)
       /\ Safety
       /\ Liveness

===============================================================================