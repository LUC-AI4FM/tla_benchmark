---------------------------- MODULE CounterFlagMachine ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Distinguished == 5

UpperBound == 10

Init ==
    /\ x \in 1..3
    /\ y = 0

Increment ==
    /\ x' = x + 1
    /\ UNCHANGED y

Stutter ==
    /\ x \in Nat
    /\ x' = x
    /\ UNCHANGED y

SetDistinguished ==
    /\ x' = Distinguished
    /\ y' \in {0, 1}

Decrease ==
    /\ x > 0
    /\ \E k \in 1..2 :
         /\ k <= x
         /\ x' = x - k
    /\ UNCHANGED y

InertFalse ==
    /\ FALSE
    /\ x' = x + 100
    /\ UNCHANGED y

InertUnreachable ==
    /\ x < 0
    /\ x' = 0
    /\ y' = 0

Next ==
    \/ Increment
    \/ Stutter
    \/ SetDistinguished
    \/ Decrease
    \/ InertFalse
    \/ InertUnreachable

Spec == Init /\ [][Next]_vars

Constraint == x < UpperBound

Inv ==
    /\ x \in Nat
    /\ y \in Nat

Inv2 ==
    /\ \A S \in SUBSET (0..x) :
         /\ \A e \in S : e \in 0..x /\ e <= x
         /\ Cardinality(S) <= x + 1
    /\ \A i \in 0..x : \E j \in 0..x : j = i
    /\ \A b \in 0..y : b \in Nat

=============================================================================