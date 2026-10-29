---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x \in 1..3
    /\ y = 0

A ==
    /\ y \in Nat
    /\ x \in Nat
    /\ x' = x + 1
    /\ UNCHANGED y

B ==
    /\ x \in Nat
    /\ \A S \in SUBSET (1..3) : S \subseteq 1..3
    /\ UNCHANGED vars

C ==
    /\ x = 42
    /\ x' = TRUE
    /\ y' = FALSE

D ==
    /\ x \in Nat
    /\ x' \in 0..x
    /\ UNCHANGED y

U1 ==
    /\ x \in Nat
    /\ x < 0
    /\ UNCHANGED vars

U2 ==
    /\ x \in Nat
    /\ x < 0
    /\ UNCHANGED vars

U3 ==
    /\ x \in Nat
    /\ x < 0
    /\ UNCHANGED vars

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ U1
    \/ U2
    \/ U3

Spec == Init /\ [][Next]_vars

Constraint == x \in Nat /\ x < 20

Inv ==
    /\ x \in Nat
    /\ y \in Nat
    /\ \A S \in SUBSET (1..5) : Cardinality(S) <= 5
    /\ \E T \in SUBSET (1..4) : T = {}
    /\ IF TRUE THEN (IF TRUE THEN TRUE ELSE FALSE) ELSE FALSE

Inv2 ==
    /\ x \in Nat
    /\ y \in Nat
    /\ \A S \in SUBSET (1..4) : \A e \in S : e \in 1..4
    /\ \E T \in SUBSET (1..3) : Cardinality(T) >= 0
    /\ (TRUE => (TRUE \/ FALSE))

THEOREM Spec => [](Inv /\ Inv2)
=============================================================================