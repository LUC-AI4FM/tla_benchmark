---------------------------- MODULE NextStateExpressions ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT MaxX

ASSUME MaxXAssumption == MaxX \in Nat /\ MaxX >= 2

VARIABLES x, y

vars == <<x, y>>

-----------------------------------------------------------------------------
(* Type invariant: both components are always valid integers.               *)
-----------------------------------------------------------------------------
TypeOK == /\ x \in Int
          /\ y \in Int
          /\ x \in 1..MaxX
          /\ y = 1

-----------------------------------------------------------------------------
(* Initial state                                                            *)
-----------------------------------------------------------------------------
Init == /\ x = 1
        /\ y = 1

-----------------------------------------------------------------------------
(* Transition branches                                                      *)
-----------------------------------------------------------------------------

\* Branch 1: only the first component changes.
IncXOnly ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ UNCHANGED y

\* Branch 2: the first component increases, and the second component is
\* constrained by the NEW value of the first component.
IncXConstrainY ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ IF x' = 2 THEN y' = 1 ELSE y' = y

\* Branch 3: the first component increases, and the second component is
\* deterministically reset to 1.
IncXResetY ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ y' = 1

\* Branch 4: guarded nondeterministic choice with an embedded assertion.
\* The conjunct y' \in {1} acts as an assertion: the sub-branch d = 1 would
\* violate it and is therefore disallowed; only d = 0 is enabled.
GuardedChoice ==
    /\ x < MaxX
    /\ \E d \in {0, 1} :
          /\ x' = x + 1
          /\ y' = y + d
          /\ y' \in {1}          \* assertion enforced in the branch

\* Terminal stuttering once the bound is reached (avoids deadlock reports).
Done ==
    /\ x = MaxX
    /\ UNCHANGED vars

Next == \/ IncXOnly
        \/ IncXConstrainY
        \/ IncXResetY
        \/ GuardedChoice
        \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties over next-state expressions (action properties)        *)
-----------------------------------------------------------------------------

\* The second component is always a valid integer in every transition.
YAlwaysInt == [][y' \in Int]_vars

\* Conditional consistency: if the first component's new value is 2 in a
\* transition, then the second component's new value must be 1.
CondConsistency == [][(x' = 2) => (y' = 1)]_vars

\* No contradictory next-state constraints: x' never equals two different
\* integers simultaneously, and every real step increments x by exactly one.
NoContradiction ==
    [][ /\ ~(x' = 2 /\ x' = 3)
        /\ x' = x + 1 ]_vars

\* Well-formedness of set- and function-valued expressions using primes.
f == [i \in {1, 2} |-> i]

SetFunWellFormed ==
    [][ /\ x' \in {x + 1}                               \* membership
        /\ {x'} \subseteq Int                           \* subset
        /\ {x', y'} \subseteq 1..MaxX                   \* subset (bounded)
        /\ DOMAIN [f EXCEPT ![1] = x'] = {1, 2}         \* domain preserved
        /\ [f EXCEPT ![1] = x'][1] = x'                 \* updated value
        /\ [f EXCEPT ![2] = y'][2] = y'                 \* updated value
        /\ [f EXCEPT ![1] = x'][2] = f[2]               \* untouched value
        /\ Cardinality({x', y'}) \in {1, 2} ]_vars

\* Assertions embedded in guarded choices are enforced: no transition can
\* produce a second-component value other than 1.
AssertionEnforced == [][y' = 1]_vars

-----------------------------------------------------------------------------
(* Liveness / reachability exploration                                      *)
-----------------------------------------------------------------------------

\* The system eventually leaves the initial state, demonstrating at least
\* two distinct reachable states.
LeavesInit == <>(x # 1)

\* The system eventually reaches the state where x = 2 (second distinct state).
ReachesTwo == <>(x = 2 /\ y = 1)

\* The system eventually reaches the bound.
ReachesMax == <>(x = MaxX)

\* Helper invariant whose violation exhibits a non-initial reachable state
\* (check as an invariant to obtain a witness trace with >= 2 states).
OnlyInitialState == x = 1 /\ y = 1

THEOREM Spec => []TypeOK
THEOREM Spec => YAlwaysInt /\ CondConsistency /\ NoContradiction
                 /\ SetFunWellFormed /\ AssertionEnforced
THEOREM Spec => LeavesInit /\ ReachesTwo /\ ReachesMax
=============================================================================