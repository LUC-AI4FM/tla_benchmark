---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Init == /\ x \in 1..3
        /\ y = 0

A == /\ x \in Nat
     /\ y \in Nat
     /\ x' = x + 1
     /\ y' = y

B == /\ x \in Nat
     /\ \A s \in SUBSET (1..3) : s \subseteq (1..3)
     /\ UNCHANGED vars

C == /\ x = 42
     /\ x' = TRUE
     /\ y' = FALSE

D == /\ x \in Nat
     /\ x' \in 0..x
     /\ UNCHANGED y

U1 == /\ x < 0
      /\ UNCHANGED vars

U2 == /\ x < 0
      /\ UNCHANGED vars

U3 == /\ x < 0
      /\ UNCHANGED vars

Next == A \/ B \/ C \/ D \/ U1 \/ U2 \/ U3

Spec == Init /\ [][Next]_vars

Constraint == x < 20

Inv == /\ x \in Nat
       /\ y \in Nat
       /\ \A s \in SUBSET (1..4) : Cardinality(s) <= 4
       /\ IF TRUE THEN (IF TRUE THEN TRUE ELSE FALSE) ELSE FALSE

Inv2 == /\ x \in Nat
        /\ y \in Nat
        /\ \E s \in SUBSET (1..5) : s = {}
        /\ \A s \in SUBSET (1..3) : \A t \in SUBSET s : t \subseteq s
        /\ (TRUE \/ FALSE) /\ ((TRUE => TRUE) /\ ~FALSE)

=============================================================================