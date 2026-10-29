---- MODULE CoverageStatistics ----
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x \in 1..3
    /\ y = 0

\* Increment: primary counter incremented, secondary unchanged.
A ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* No-op: both counters unchanged (several equivalent formulations).
B ==
    /\ x \in Nat
    /\ y \in Nat
    /\ UNCHANGED <<x, y>>

B2 ==
    /\ x \in Nat
    /\ x' = x
    /\ y' = y

B3 ==
    /\ y \in Nat
    /\ UNCHANGED vars

B4 ==
    /\ x \in Nat
    /\ UNCHANGED x
    /\ UNCHANGED y

\* Type change: when x = 42, both counters become booleans.
C ==
    /\ x = 42
    /\ x' = TRUE
    /\ y' = FALSE

\* Decrement: x non-deterministically decreases to a value in 0..x.
D ==
    /\ x \in Nat
    /\ x' \in 0..x
    /\ UNCHANGED y

\* Unreachable transitions: guarded by an impossible condition.
U1 ==
    /\ x < 0
    /\ x' = x - 1
    /\ UNCHANGED y

U2 ==
    /\ x < 0
    /\ y' = y + 1
    /\ UNCHANGED x

U3 ==
    /\ x < 0
    /\ UNCHANGED <<x, y>>

U4 ==
    /\ x < 0
    /\ x' = 0
    /\ y' = 0

Next ==
    \/ A
    \/ B
    \/ B2
    \/ B3
    \/ B4
    \/ C
    \/ D
    \/ U1
    \/ U2
    \/ U3
    \/ U4

Spec == Init /\ [][Next]_vars

\* State constraint bounding exploration for finite model checking.
Constraint == x < 20

\* Type invariants (equivalent formulations).
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

TypeOK2 ==
    x \in Nat /\ y \in Nat

TypeOK3 ==
    \A v \in {x, y} : v \in Nat

\* Deliberately expensive invariants iterating over power sets.
Inv1 ==
    /\ x \in Nat
    /\ \A S \in SUBSET (0..x) : Cardinality(S) <= x + 1

Inv2 ==
    /\ y \in Nat
    /\ \A S \in SUBSET (0..x) : \A e \in S : e <= x

Inv3 ==
    /\ x \in Nat
    /\ y \in Nat
    /\ \E S \in SUBSET (0..x) : Cardinality(S) = 0

Inv ==
    /\ TypeOK
    /\ Inv1
    /\ Inv2
    /\ Inv3

THEOREM Spec => []TypeOK
====