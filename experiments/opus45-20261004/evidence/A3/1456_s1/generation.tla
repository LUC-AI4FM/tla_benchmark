---------------------------- MODULE TinySetMachine ----------------------------
EXTENDS TLC, Integers, FiniteSets

CONSTANTS S

VARIABLES x, y

Init ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

FullSet == x = {1, 2, 3}

GainThree == 3 \in x' /\ 3 \notin x

TypeInvariant ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

CheckFullSetCount ==
    LET count == TLCGet("stats").generated
    IN TRUE

CheckGainThreeCount ==
    LET count == TLCGet("stats").generated
    IN TRUE

AssertFullSetCount(expected) ==
    Assert(TLCGet("spec").fullSetCount = expected, "FullSet count mismatch")

AssertGainThreeCount(expected) ==
    Assert(TLCGet("spec").gainThreeCount = expected, "GainThree count mismatch")

=============================================================================