------------------------------ MODULE OpParamCounter ------------------------------
EXTENDS Naturals, Integers

\* Fixed finite range of the counter
Min == 0
Max == 5
Range == Min..Max

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------------
\* Recursive boolean predicates that can be passed as parameters

\* Always holds for every natural input.
RECURSIVE AlwaysTrue(_)
AlwaysTrue(n) == IF n <= 0 THEN TRUE ELSE AlwaysTrue(n - 1)

\* Fails for some inputs: holds exactly for even naturals.
RECURSIVE IsEven(_)
IsEven(n) == IF n <= 0 THEN n = 0
             ELSE IF n = 1 THEN FALSE
             ELSE IsEven(n - 2)

\* Recursive predicate that is always true on the counter's range.
RECURSIVE Test(_)
Test(n) == IF n <= Min THEN n = Min ELSE Test(n - 1)

\* A unary predicate operator. It can be overridden in the config,
\* for example with Op <- Test.
Op(n) == n \in Range

\* A higher-order operator. It applies a supplied unary predicate to a value.
Op2(P(_), n) == P(n)

\* A simple arithmetic operator for composition checks.
Double(n) == 2 * n

-----------------------------------------------------------------------------------
\* Initial state and the two alternative transition semantics

Init == x = Min

\* Deterministic semantics: increment, then wrap back to Min after Max.
DetNext == x' = IF x < Max THEN x + 1 ELSE Min

\* Nondeterministic semantics: any value in the range.
NondetNext == \E v \in Range : x' = v

\* Set to FALSE to use the nondeterministic semantics.
UseDeterministic == TRUE

Next == IF UseDeterministic THEN DetNext ELSE NondetNext

SPEC == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------------
\* Correctness properties

\* Invariant: the state always remains within the finite range.
TypeOK == x \in Range

\* Parameterized safety: a supplied unary predicate holds on the current state.
StateProperty == Op(x)

\* Composition: a higher-order operator applied to a recursive predicate.
Property == Op2(Test, x)

\* Nested parameterized operators preserve the range invariant.
PropertyE == Op2(Op, x) /\ Op2(AlwaysTrue, x)

\* Composition with Double: doubling a value in the range yields an even value
\* within the doubled range.
PropertyF == Op2(IsEven, Double(x)) /\ Double(x) \in 0..Double(Max)

\* Trivial tautology for sanity checks.
PropertyG == TRUE \/ ~TRUE

\* Range invariant together with a nested application of Op2.
PropertyH == TypeOK /\ Op2(LAMBDA n : Op2(Op, n), x)

\* Liveness: the system keeps making transitions and never deadlocks.
Liveness == []<>(x = Min) /\ []<>(x = Max)

=============================================================================