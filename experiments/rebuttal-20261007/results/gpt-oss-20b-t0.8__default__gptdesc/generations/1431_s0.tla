--------------------------- MODULE TwoStateHistory ----------------------------
EXTENDS Naturals, Sequences

CONSTANT MAX_HIST

VARIABLES pc, hist

Init == /\ pc = "A"
        /\ hist = << >>

ActionA == /\ pc = "A"
           /\ pc' = "B"
           /\ hist' = Append(hist, "A")

ActionB == /\ pc = "B"
           /\ pc' = "A"
           /\ hist' = hist

Stutter == /\ pc' = pc
            /\ hist' = hist

Next == ActionA \/ ActionB \/ Stutter

Inv == Len(hist) <= MAX_HIST

Spec == Init /\ [][Next]_vars /\ WF_vars(ActionA \/ ActionB) /\ Inv

Liveness == <> (pc = "Done")
=============================================================================