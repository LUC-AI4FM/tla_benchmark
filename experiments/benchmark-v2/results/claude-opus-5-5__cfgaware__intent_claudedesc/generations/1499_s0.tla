---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x \in 1..3
    /\ y = 0

\* Increment the primary counter; secondary unchanged.
A ==
    /\ x' = x + 1
    /\ y' = y

\* No-op: both counters unchanged (always enabled when counters are naturals).
B ==
    /\ x \in Nat
    /\ y \in Nat
    /\ UNCHANGED vars

\* Type change / mode switch when x = 42.
C ==
    /\ x = 42
    /\ x' = TRUE
    /\ y' = FALSE

\* Non-deterministic decrement to any value in 0..x.
D ==
    /\ x' \in 0..x
    /\ UNCHANGED y

\* Unreachable transitions (guard can never hold from valid initial states).
U1 ==
    /\ x < 0
    /\ x' = x + 1
    /\ UNCHANGED <<y>>

U2 ==
    /\ x < 0
    /\ UNCHANGED x
    /\ UNCHANGED y

U3 ==
    /\ x < 0
    /\ x' = x
    /\ y' = y

U4 ==
    /\ x < 0
    /\ <<x', y'>> = <<x, y>>

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ U1
    \/ U2
    \/ U3
    \/ U4

Spec == Init /\ [][Next]_vars

\* State constraint bounding exploration.
Constraint == x < 20

\* Type invariant with a deliberately expensive power-set iteration.
Inv ==
    /\ x \in Nat
    /\ y \in Nat
    /\ \A s \in SUBSET (1..x) : s \subseteq Nat

\* Equivalent formulation of the invariant with different syntax and
\* another deliberately expensive power-set computation.
Inv2 ==
    /\ \A v \in {x, y} : v \in Nat
    /\ ~(x \notin Nat \/ y \notin Nat)
    /\ \A s \in SUBSET (0..x) : Cardinality(s) >= 0

=============================================================================