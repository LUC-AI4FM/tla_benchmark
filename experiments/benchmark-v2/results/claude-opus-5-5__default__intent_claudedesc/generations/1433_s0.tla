------------------------------ MODULE InitStateGeneration ------------------------------
(***************************************************************************)
(* A test harness for exploring how a TLA+ model checker generates initial *)
(* states for an Init predicate built from conjunctions, disjunctions,     *)
(* tautologies, double negation, unsatisfiable clauses, and assignments.   *)
(*                                                                         *)
(* The system has one variable x. Each disjunct of Init is a separate      *)
(* initialization clause that shows one syntactic pattern. After           *)
(* initialization the system only stutters.                                *)
(*                                                                         *)
(* The set of initial states should be exactly {1, 2, 3, 5, 6, 7}, with    *)
(* each state appearing exactly once. Clause 4 is unsatisfiable, so it     *)
(* contributes no state.                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

VARIABLES x

vars == << x >>

\* Bounded universe of candidate values, used only for the static checks.
Universe == 0 .. 10

(***************************************************************************)
(* Initialization clauses, parameterized by the value v of x.              *)
(***************************************************************************)

\* 1. Assignment followed by a tautological disjunction.
\*    The second disjunct "v = 1" duplicates the assignment. A naive
\*    checker that explores both branches could produce x = 1 twice.
Clause1(v) == /\ v = 1
              /\ (TRUE \/ v = 1)

\* 2. Tautological disjunction followed by an assignment.
\*    The branch "v = 2" may be taken before the assignment conjunct, so
\*    the checker may treat it as the assignment itself.
Clause2(v) == /\ (TRUE \/ v = 2)
              /\ v = 2

\* 3. Logically transformed tautology (double negation) with an assignment.
Clause3(v) == /\ v = 3
              /\ ~~(TRUE \/ v = 3)

\* 4. Assignment combined with an unsatisfiable disjunction. Produces no state.
Clause4(v) == /\ v = 4
              /\ (FALSE \/ (v # v))

\* 5. Nested disjunctions with mixed satisfiability.
Clause5(v) == /\ v = 5
              /\ ((FALSE \/ v = 5) \/ (TRUE \/ FALSE))

\* 6. Simple direct assignment.
Clause6(v) == v = 6

\* 7. Double negation wrapped around the assignment itself.
Clause7(v) == ~~(v = 7) /\ ~(FALSE /\ v = 7)

InitPred(v) == \/ Clause1(v)
               \/ Clause2(v)
               \/ Clause3(v)
               \/ Clause4(v)
               \/ Clause5(v)
               \/ Clause6(v)
               \/ Clause7(v)

ExpectedInitStates == {1, 2, 3, 5, 6, 7}

UnsatisfiableValues == {4}

(***************************************************************************)
(* Static sanity checks on the semantics of Init. These are independent of *)
(* the order in which the checker enumerates branches.                     *)
(***************************************************************************)
ASSUME {v \in Universe : InitPred(v)} = ExpectedInitStates
ASSUME {v \in Universe : Clause4(v)} = {}
ASSUME \A v \in Universe : Clause1(v) <=> (v = 1)
ASSUME \A v \in Universe : Clause2(v) <=> (v = 2)
ASSUME \A v \in Universe : Clause3(v) <=> (v = 3)
ASSUME \A v \in Universe : Clause5(v) <=> (v = 5)
ASSUME \A v \in Universe : Clause6(v) <=> (v = 6)
ASSUME \A v \in Universe : Clause7(v) <=> (v = 7)
\* Each expected state is produced by exactly one clause, so it is non-redundant.
ASSUME \A e \in ExpectedInitStates :
         Cardinality({i \in 1..7 :
             CASE i = 1 -> Clause1(e)
               [] i = 2 -> Clause2(e)
               [] i = 3 -> Clause3(e)
               [] i = 4 -> Clause4(e)
               [] i = 5 -> Clause5(e)
               [] i = 6 -> Clause6(e)
               [] i = 7 -> Clause7(e)}) = 1

(***************************************************************************)
(* Behavior                                                                *)
(***************************************************************************)
Init == InitPred(x)

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK == x \in Nat

\* Only the expected initial states are reachable.
OnlyExpectedStates == x \in ExpectedInitStates

\* The unsatisfiable clause never contributes a state.
NoUnsatisfiableState == x \notin UnsatisfiableValues

\* Every reachable state satisfies Init, because the system only stutters.
AlwaysInit == InitPred(x)

(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)
\* x never changes after initialization.
StaticBehavior == [][x' = x]_vars

\* Once x holds a value, it holds that value forever.
Stability == \A v \in ExpectedInitStates : [](x = v => [](x = v))

THEOREM Spec => [](TypeOK /\ OnlyExpectedStates /\ NoUnsatisfiableState /\ AlwaysInit)
THEOREM Spec => StaticBehavior
=============================================================================