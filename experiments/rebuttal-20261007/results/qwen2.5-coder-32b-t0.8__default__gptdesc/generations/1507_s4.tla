------------------------------- MODULE TinyClock -------------------------------
EXTENDS Naturals

CONSTANTS
    \* No constants needed for this simple system

VARIABLES clock

Check(v) == \/ v = TRUE \/ v = FALSE
Flip(v)  == IF v = TRUE THEN FALSE ELSE TRUE

Init == Check(clock)

Next == /\ Check(clock)
        /\ clock' = Flip(clock)

Spec == Init /\ [][Next]_<<clock>>

\* Safety invariants
INV_ClockBoolean == clock \in {TRUE, FALSE}

\* Liveness properties
LIVENESS_Flip == <>[](clock' # clock)  \* Clock eventually flips

\* Fairness conditions
WF_CLOCK == WF_<>(Next)

================================================================================