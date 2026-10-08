------------------------------- MODULE ClockSystem ------------------------------

EXTENDS Naturals

CONSTANTS TRUE, FALSE

VARIABLES clock

Check(c) == c \in {TRUE, FALSE}
Flip(c)  == IF c = TRUE THEN FALSE ELSE TRUE

Init == Check(clock) \* TLC will cover this with one recursive call for each constant in the set.

Next == /\ Check(clock)
        /\ clock' = Flip(clock)

Spec ==
    /\ Init
    /\ [][Next]_<<clock>>

Invariant == clock \in {TRUE, FALSE}

Fairness == WF_next

================================================================================