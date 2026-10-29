---------------------------- MODULE BoundedCounterFlag ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Bound,      \* strict upper bound on the counter
    Special,    \* distinguished constant the counter may be reset to
    MaxDec      \* maximum amount by which the counter may be decreased in one step

ASSUME BoundAssumption   == Bound \in Nat /\ Bound > 3
ASSUME SpecialAssumption == Special \in Nat /\ Special < Bound
ASSUME MaxDecAssumption  == MaxDec \in Nat /\ MaxDec > 0

VARIABLES
    x,  \* bounded counter
    y   \* flag / secondary value (Booleans encoded as 0 = FALSE, 1 = TRUE)

vars == << x, y >>

BoolVals == {0, 1}

-----------------------------------------------------------------------------------
\* Initial condition: counter in a small positive range, secondary value zero.

Init ==
    /\ x \in 1..3
    /\ y = 0

-----------------------------------------------------------------------------------
\* (a) Increment the counter, staying strictly below Bound.
Increment ==
    /\ x + 1 < Bound
    /\ x' = x + 1
    /\ UNCHANGED y

\* (b) Leave the counter unchanged while checking side-conditions
\*     that do not affect the secondary component.
SideCondition ==
    /\ x \in Nat
    /\ y \in Nat
    /\ x' = x
    /\ y' = y

\* (c) Set the counter to the distinguished constant and change the
\*     secondary component to a Boolean value.
SetSpecial ==
    /\ x' = Special
    /\ y' \in BoolVals

\* (d) Decrease the counter nondeterministically within a bounded range.
Decrease ==
    /\ x > 0
    /\ \E d \in 1..MaxDec :
          /\ d <= x
          /\ x' = x - d
    /\ UNCHANGED y

\* Deliberately inert transitions modelling spurious / unreachable branches.
NoOp ==
    UNCHANGED vars

Spurious ==
    /\ x >= Bound            \* never enabled in reachable states
    /\ x' = x + 1
    /\ UNCHANGED y

Unreachable ==
    /\ FALSE
    /\ x' = Bound
    /\ y' = Bound

-----------------------------------------------------------------------------------
\* Global next-state relation.

Next ==
    \/ Increment
    \/ SideCondition
    \/ SetSpecial
    \/ Decrease
    \/ NoOp
    \/ Spurious
    \/ Unreachable

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Safety invariants.

\* Both state components remain natural numbers.
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

\* Global numeric constraint: counter strictly below the upper bound.
BoundInv ==
    x < Bound

\* Secondary component only ever holds Boolean-encoded values.
FlagInv ==
    y \in BoolVals

\* Expensive, purely logical invariant quantifying over finite sets and ranges.
QuantifiedInv ==
    /\ \A S \in SUBSET (0..x) :
          /\ \A e \in S : e <= x /\ e < Bound
          /\ Cardinality(S) <= x + 1
    /\ \A i \in 0..x : \E j \in 0..Bound : j = i + 1
    /\ \A T \in SUBSET BoolVals : y \in T \/ y \notin T

Inv ==
    /\ TypeOK
    /\ BoundInv
    /\ FlagInv
    /\ QuantifiedInv

-----------------------------------------------------------------------------------
\* Correctness statements.

THEOREM Spec => []TypeOK
THEOREM Spec => []BoundInv
THEOREM Spec => []QuantifiedInv
THEOREM Spec => [][Next]_vars

===================================================================================