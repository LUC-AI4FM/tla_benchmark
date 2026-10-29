---------------------------- MODULE Increment ----------------------------
EXTENDS Naturals

VARIABLE x

vars == << x >>

\* Optional bounds. These are operator definitions rather than CONSTANTs so
\* the module binds without extra configuration.
\*   InitBound     : finite stand-in for "any natural number" in initial states
\*   MaxValue      : upper bound used by the bounded variant
\*   UseBound      : TRUE selects the bounded variant, FALSE the unbounded one
InitBound == 3
MaxValue  == 10
UseBound  == TRUE

---------------------------------------------------------------------------
\* Type / state space

TypeOK == x \in Nat

---------------------------------------------------------------------------
\* Initial states

\* Abstract initial predicate: x may be any natural number.
AbstractInit == x \in Nat

\* Finite initial predicate for explicit-state model checking.
Init == x \in 0..InitBound

---------------------------------------------------------------------------
\* Actions

\* Increment x by exactly one. Nothing else changes.
xplus1 == x' = x + 1

Next == xplus1

\* Stuttering steps (x' = x) are permitted by [Next]_vars.
Spec == Init /\ [][Next]_vars /\ WF_vars(xplus1)

AbstractSpec == AbstractInit /\ [][Next]_vars /\ WF_vars(xplus1)

\* Spec without fairness. It permits infinite stuttering.
SafetySpec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
\* Bounded and unbounded variants

\* State constraint for model checking the bounded variant.
\* If UseBound is FALSE, the state space is unbounded.
StateConstraint == UseBound => x <= MaxValue

\* Invariant relating x to the upper bound. It is meaningful under the
\* bounded variant, where the constraint limits exploration.
BoundInv == UseBound => x <= MaxValue + 1

---------------------------------------------------------------------------
\* Correctness properties

\* Safety: x is always a natural number.
Safety == TypeOK

\* Monotonicity: every step that changes x increases it by exactly one.
Monotonicity == [][x' # x => x' = x + 1]_vars

\* No unintended jumps: every step changes x by 0 or by +1.
NoJumps == [][x' = x \/ x' = x + 1]_vars

\* The increment action is always enabled.
IncrementEnabled == ENABLED xplus1

\* Liveness: from any reachable state, another increment eventually occurs.
Liveness == []<><<xplus1>>_vars

\* Alternative liveness formulation: x always eventually grows.
EventuallyGrows == \A n \in Nat : (x = n) ~> (x > n)

THEOREM Spec => []TypeOK
THEOREM Spec => Monotonicity /\ NoJumps
THEOREM Spec => Liveness
===========================================================================