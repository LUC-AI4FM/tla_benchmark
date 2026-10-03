--------------------- MODULE TinyStateMachine ---------------------
EXTENDS TLC, Integers, FiniteSets

VARIABLES x, y

S == {1, 2, 3}

TypeOK ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

Init ==
    /\ x \in SUBSET {1, 2}
    /\ y \in SUBSET S

\* Predicate to check if x is the full set {1, 2, 3}.
FullSet == x = S

\* Predicate to check if the element 3 is gained in a transition.
GainThree == (3 \notin x) /\ (3 \in x')

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'
    /\ TLCSet("gain", GainThree)

\* Helper to detect when TLC has finished exploring the state space.
IsDone == TLCGet("generated") = TLCGet("distinct")

Inv ==
    /\ TypeOK
    /\ TLCSet("full", FullSet)
    /\ (IsDone => /\ TLCGet("full") = 1     \* There is 1 state where x = {1,2,3}.
                   /\ TLCGet("gain") = 25)    \* There are 25 transitions that add 3 to x.

=============================================================================