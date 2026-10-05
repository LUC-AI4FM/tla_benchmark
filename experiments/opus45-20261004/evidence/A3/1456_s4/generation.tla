---------------------------- MODULE TinyStateMachine ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS S

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \subseteq S
    /\ y \subseteq S

Init ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

Next ==
    /\ y' = y
    /\ x' \in {s \in SUBSET S : s \subseteq y'}

FullSet == x = {1, 2, 3}

GainThree == /\ 3 \notin x
             /\ 3 \in x'

CheckCounts ==
    /\ TLCGet("stats").generated > 0

Inv == TypeOK

=============================================================================