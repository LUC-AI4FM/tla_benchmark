---------------------------- MODULE TinyClock ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    \* No constants defined in this specification

VARIABLES
    clock

Check(c) == c \in {TRUE, FALSE}

Flip(c) == IF c = TRUE THEN FALSE ELSE TRUE

Init == Check(clock)
        \* TLC will cover the call to Check in Init

Next == /\ Check(clock)
      /\ clock' = Flip(clock)

Spec == SpecFair(Init, Next)

=============================================================================