---------------------------- MODULE specification ----------------------------

EXTENDS Integers, TLC, FiniteSets

VARIABLES x, y

S == {1, 2, 3}

TypeOK == x \subseteq S /\ y \subseteq S

Init == x \in SUBSET S /\ y \in SUBSET S

Next == y' = y /\ x' \in SUBSET y'

FullSet == x = {1, 2, 3}

GainThree == 3 \notin x /\ 3 \in x'

Inv == TypeOK /\
       (TLCGet("level") > 0 => 
        (TLCGet("stats").generated >= 0))

=============================================================================