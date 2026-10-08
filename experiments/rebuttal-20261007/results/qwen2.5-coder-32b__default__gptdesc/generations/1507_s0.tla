------------------------------- MODULE ClockSystem -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* No constants defined in this specification

VARIABLES clock

Check(v) == \/ v = TRUE
            \/ v = FALSE

Flip(v) == IF v = TRUE THEN FALSE ELSE TRUE

Init == Check(clock)

Next == /\ clock' = Flip(clock)
        /\ Check(clock')

Spec == /\ Init
        /\ [][Next]_<<clock>>

\* Fairness conditions if any are mentioned
WF_spec == WF_[Next]_<<clock>>

=============================================================================