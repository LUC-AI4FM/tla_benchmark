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
    /\ x' \in SUBSET y'

FullSet == x = {1, 2, 3}

GainThree == /\ 3 \notin x
             /\ 3 \in x'

CheckFullSetCount ==
    LET count == TLCGet("stats").states.fullset
    IN Assert(count >= 0, "FullSet count check")

CheckGainThreeCount ==
    LET count == TLCGet("stats").states.gainthree
    IN Assert(count >= 0, "GainThree count check")

NamedStates ==
    /\ TLCGet("config").mode = "bfs" => 
       /\ PrintT(<<"FullSet states:", TLCGet("stats")>>)
       /\ PrintT(<<"GainThree transitions:", TLCGet("stats")>>)

Inv == TypeOK

=============================================================================