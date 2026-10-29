---------------------------- MODULE CoverageStateMachine ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in Nat
          /\ y \in 0..2

Init == /\ x \in 1..3
        /\ y = 0

\* (a) Update one component and leave the other unchanged.
IncX == /\ x' = x + 1
        /\ y' = y

\* (a) Update one component; the other is referenced individually as UNCHANGED.
StepY == /\ y' = (y + 1) % 3
         /\ UNCHANGED x

\* (b) Update both components.
Both == /\ x < 8
        /\ x' = x + 2
        /\ y' = 0

\* (c) Guarded stutter on the tuple.
StutterTuple == /\ y = 2
                /\ UNCHANGED <<x, y>>

\* (c) Guarded stutter with components referenced individually.
StutterSplit == /\ x > 1
                /\ UNCHANGED x
                /\ UNCHANGED y

\* Unreachable guarded transitions.
Unreachable1 == /\ x > 100
                /\ x' = 0
                /\ y' = y

Unreachable2 == /\ FALSE
                /\ UNCHANGED vars

Unreachable3 == /\ y > 2
                /\ y' = 0
                /\ UNCHANGED x

Next == \/ IncX
        \/ StepY
        \/ Both
        \/ StutterTuple
        \/ StutterSplit
        \/ Unreachable1
        \/ Unreachable2
        \/ Unreachable3

Spec == Init /\ [][Next]_vars

\* State constraint bounding one component across all reachable states.
Constraint == x < 10

\* Invariants: numeric bounds.
BoundY == y \in 0..2
BoundX == x >= 1
Inv == TypeOK /\ BoundX /\ BoundY

\* Unreachable transitions are never taken.
NeverUnreachable == [][~Unreachable1 /\ ~Unreachable2 /\ ~Unreachable3]_vars

\* UNCHANGED claims mean that the intended components do not change.
UnchangedCorrect ==
    [][ /\ (StutterTuple => (x' = x /\ y' = y))
        /\ (StutterSplit => (x' = x /\ y' = y))
        /\ (IncX => y' = y)
        /\ (StepY => x' = x) ]_vars

\* Every step conforms to one of the alternatives.
StepsConform == [][Next]_vars
=====================================================================================