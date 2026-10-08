------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals

CONSTANTS A, N

VARIABLES x, y, initB

Init == /\ initB \in 1..N
        /\ x = A
        /\ y = initB

Swap ==
    /\ x < y
    /\ x' = y
    /\ y' = x

Subtract ==
    /\ x >= y
    /\ y > 0
    /\ x' = x - y
    /\ y' = y

Next == Swap \/ Subtract

vars == <<x, y, initB>>

NatBounds ==
    /\ x \in Nat
    /\ y \in Nat

CommonDivisorsInvariant ==
    \A d \in Nat :
        (d > 0) => ((x % d = 0 /\ y % d = 0) <=> (A % d = 0 /\ initB % d = 0))

Invariant == NatBounds /\ CommonDivisorsInvariant

TerminationCorrect ==
    (x = 0 /\ \A d \in Nat :
        (d > 0) => ((y % d = 0) <=> (A % d = 0 /\ initB % d = 0))) \/ 
    (y = 0 /\ \A d \in Nat :
        (d > 0) => ((x % d = 0) <=> (A % d = 0 /\ initB % d = 0)))

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ []Invariant
    /\ <> (x = 0 \/ y = 0)
    /\ []((x = 0 \/ y = 0) => TerminationCorrect)

=============================================================================