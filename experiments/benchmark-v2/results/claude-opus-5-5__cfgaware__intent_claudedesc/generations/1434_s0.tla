---------------------------- MODULE TLCStateGen ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

\* Counter registers used to record how often TLC considers each transition.
C1 == 1   \* assignment before disjunction of TRUE conditions
C2 == 2   \* assignment after disjunction of TRUE conditions
C3 == 3   \* double negation forcing eager evaluation
C4 == 4   \* disjunction of FALSE conditions (unsatisfiable)
C5 == 5   \* simple disjunction, branch x' = 5
C6 == 6   \* simple disjunction, branch x' = 6

Count(i) == TLCSet(i, TLCGet(i) + 1)

Init ==
    /\ x = 0
    /\ TLCSet(C1, 0)
    /\ TLCSet(C2, 0)
    /\ TLCSet(C3, 0)
    /\ TLCSet(C4, 0)
    /\ TLCSet(C5, 0)
    /\ TLCSet(C6, 0)

\* Assignment appears before a disjunction of always-true conditions.
AssignBeforeOr ==
    /\ x = 0
    /\ x' = 1
    /\ (TRUE \/ TRUE)
    /\ Count(C1)

\* Assignment appears after a disjunction of always-true conditions.
AssignAfterOr ==
    /\ x = 0
    /\ (TRUE \/ TRUE)
    /\ x' = 2
    /\ Count(C2)

\* Double negation forces eager evaluation of the disjunction.
DoubleNeg ==
    /\ x = 0
    /\ ~~(TRUE \/ TRUE)
    /\ x' = 3
    /\ Count(C3)

\* Disjunction of always-false conditions: this branch is unsatisfiable.
Unsat ==
    /\ x = 0
    /\ x' = 4
    /\ (FALSE \/ FALSE)
    /\ Count(C4)

\* Simple disjunction between different variable assignments.
SimpleOr ==
    /\ x = 0
    /\ \/ (x' = 5 /\ Count(C5))
       \/ (x' = 6 /\ Count(C6))

Next ==
    \/ AssignBeforeOr
    \/ AssignAfterOr
    \/ DoubleNeg
    \/ Unsat
    \/ SimpleOr

Spec == Init /\ [][Next]_vars

ExpectedStates == {0, 1, 2, 3, 5, 6}

\* State space integrity: exactly the intended states are reachable,
\* and the unsatisfiable successor (4) never appears.
Inv ==
    /\ x \in ExpectedStates
    /\ x # 4

\* State predicate identifying the state reached through the simple disjunction.
HasFive == x = 5

\* Action identifying a transition leaving the initial state.
LeaveInit == x = 0 /\ x' # 0

\* Every step taken from the initial state goes to an intended successor.
_POSSIBLE == [][x = 0 => x' \in ExpectedStates \ {0}]_vars

\* Transition counting: each satisfiable transition is considered at least
\* once, and the unsatisfiable transition is never counted.
PossibleCounts ==
    /\ TLCGet(C1) >= 1
    /\ TLCGet(C2) >= 1
    /\ TLCGet(C3) >= 1
    /\ TLCGet(C4) = 0
    /\ TLCGet(C5) >= 1
    /\ TLCGet(C6) >= 1

=============================================================================