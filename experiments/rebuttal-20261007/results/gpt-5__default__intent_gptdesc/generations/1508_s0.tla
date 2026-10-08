----------------------------- MODULE SingleIntStateMachine -----------------------------

EXTENDS Naturals, Integers

CONSTANTS
    N,        \* Upper bound of the finite natural-number domain
    InitVal,  \* Unique initial value
    LO, HI,   \* Subrange bounds for a nondeterministic assignment
    G,        \* Guard value for a guarded transition
    G1, G2    \* Choices enabled only when x = G (may be in or out of domain)

ASSUME
    /\ N \in Nat
    /\ InitVal \in 0..N
    /\ LO \in 0..N
    /\ HI \in 0..N
    /\ LO <= HI
    /\ HI <= N
    /\ G \in 0..N
    /\ G1 \in Int
    /\ G2 \in Int
    /\ G1 # G2

VARIABLES x

Domain == 0..N

TypeOK == x \in Domain

Init == x = InitVal

SetZero ==
    x' = 0

SetInRange ==
    x' \in LO..HI

GuardedChoice ==
    /\ x = G
    /\ x' \in {G1, G2}

IncrementIfPossible ==
    /\ x < N
    /\ x' = x + 1

ContradictoryChoice ==
    x' \in {-1, N + 5}

AllowedNext ==
    SetZero
    \/ SetInRange
    \/ GuardedChoice
    \/ IncrementIfPossible
    \/ ContradictoryChoice

Next ==
    /\ AllowedNext
    /\ TypeOK'  \* Enforce the bounded natural-number type on next states

Spec ==
    Init /\ [][Next]_x

\* Safety properties to verify
InitValueInv == x = InitVal
SafetyInv == TypeOK /\ InitValueInv

=======================================================================================