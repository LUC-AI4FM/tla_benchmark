---------------------------- MODULE PositiveAssign ----------------------------
EXTENDS Naturals

VARIABLE x

vars == << x >>

\* Sentinel for "no concrete numeric value" in the initial state
NoVal == "undefined"

\* The candidate values an assignment step may choose
Choices == {0, 1}

\* The guard that forbids accepting the zero assignment
Accept(v) == v > 0

\* Set of possible next-state values when an assignment is accepted
PossibleNext == { v \in Choices : Accept(v) }

Init == x = NoVal

\* A step nondeterministically picks 0 or 1. It is accepted only when the
\* chosen value is strictly positive. Choosing 0 is not enabled, so it
\* produces no state change (only stuttering).
Assign(v) == /\ Accept(v)
             /\ x' = v

Next == \E v \in Choices : Assign(v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Properties

TypeOK == x \in {NoVal} \cup Choices

\* (1) Safety: x is never set to a value other than 0 or 1
Safety == x # NoVal => x \in Choices

\* The possible next values are exactly the singleton positive value
SingletonNext == PossibleNext = {1}

\* (2) Consistency: every accepting assignment yields the positive option
AcceptPositive == [][ (x' # x) => (x' = 1 /\ x' \in PossibleNext) ]_vars

\* (3) Invariance: once x attains the positive value it stays legal
StaysLegal == [][ (x = 1) => (x' \in Choices) ]_vars

StaysLegalLive == [](x = 1 => [](x \in Choices))

THEOREM Spec => []TypeOK /\ []Safety /\ AcceptPositive /\ StaysLegal
=============================================================================