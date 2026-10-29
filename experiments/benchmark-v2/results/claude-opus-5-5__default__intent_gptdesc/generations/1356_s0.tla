---- MODULE CyclicCounter ----
EXTENDS Naturals

CONSTANTS
    Min,          \* lowest counter value
    Max,          \* highest counter value
    UseNondet,    \* FALSE = deterministic increment-and-wrap; TRUE = nondeterministic choice in range
    ExtPred(_),   \* externally supplied unary predicate operator
    ExtOp(_)      \* externally supplied constant operator (value -> value)

ASSUME MinMaxAssump == Min \in Nat /\ Max \in Nat /\ Min < Max
ASSUME ModeAssump   == UseNondet \in BOOLEAN

VARIABLE x

vars  == <<x>>
Range == Min..Max

-----------------------------------------------------------------------------
(* Transition semantics                                                     *)

Init == x = Min

DetStep    == x' = IF x = Max THEN Min ELSE x + 1

NondetStep == x' \in Range /\ x' # x

Next ==
    \/ (~UseNondet /\ DetStep)
    \/ ( UseNondet /\ NondetStep)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Recursive boolean predicates usable as parameters                        *)

RECURSIVE AlwaysTrue(_)
AlwaysTrue(n) == IF n <= 0 THEN TRUE ELSE AlwaysTrue(n - 1)

RECURSIVE IsEven(_)
IsEven(n) == IF n = 0 THEN TRUE
             ELSE IF n = 1 THEN FALSE
             ELSE IsEven(n - 2)

InRangeP(v) == v \in Range

-----------------------------------------------------------------------------
(* Higher-order (parameterized) operators                                   *)

\* Apply a unary predicate operator to the current state.
Holds(P(_)) == P(x)

\* Apply an operator to a value.
Apply(Op(_), v) == Op(v)

\* Conjunction of two predicate operators at a value.
AndP(P(_), Q(_), v) == P(v) /\ Q(v)

\* Implication between two predicate operators at a value.
ImpliesP(P(_), Q(_), v) == P(v) => Q(v)

\* Apply a predicate after transforming the value with an operator.
AfterOp(P(_), F(_), v) == P(F(v))

\* Temporal lifting: predicate always true on every reachable state.
AlwaysHolds(P(_)) == [](P(x))

-----------------------------------------------------------------------------
(* Safety invariants                                                        *)

TypeOK == x \in Range

\* Parameterized safety instances
InvInRange       == Holds(InRangeP)
InvAlwaysTrue    == Holds(AlwaysTrue)
InvExtPred       == Holds(ExtPred)              \* checks the externally supplied predicate
InvExtOpInRange  == AfterOp(InRangeP, ExtOp, x) \* ExtOp must map the state into Range
InvEvenFails     == Holds(IsEven)               \* expected to FAIL (odd states reachable)

\* Composition: nested parameterized operators preserve invariants
InvNested ==
    Holds(LAMBDA v : AndP(InRangeP, AlwaysTrue, v))

InvNestedApply ==
    Apply(LAMBDA v : Apply(LAMBDA w : AndP(InRangeP, AlwaysTrue, w), v), x)

InvNestedImplies ==
    Holds(LAMBDA v : ImpliesP(InRangeP, LAMBDA w : AndP(AlwaysTrue, InRangeP, w), v))

\* Trivial tautologies for sanity checks
Tautology        == TRUE
TautologyExcl    == \A b \in BOOLEAN : b \/ ~b
TautologyPred    == Holds(LAMBDA v : v = v)

-----------------------------------------------------------------------------
(* Temporal properties                                                      *)

\* No deadlock: a transition is always enabled
NoDeadlock == [](ENABLED Next)

\* Liveness: system keeps making (non-stuttering) transitions forever
Progress == []<><<Next>>_vars

\* Deterministic mode visits the minimum infinitely often
CyclesBack == ~UseNondet => []<>(x = Min)

\* Parameterized safety expressed temporally
AlwaysInRange    == AlwaysHolds(InRangeP)
AlwaysTrueProp   == AlwaysHolds(AlwaysTrue)
AlwaysExtPred    == AlwaysHolds(ExtPred)
AlwaysNested     == AlwaysHolds(LAMBDA v : AndP(InRangeP, AlwaysTrue, v))

THEOREM Spec => []TypeOK
THEOREM Spec => []InvNested
=============================================================================