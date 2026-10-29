---------------------------- MODULE PrimeSemantics ----------------------------
(***************************************************************************)
(* Test harness for the semantics of the prime operator (') in TLA+.       *)
(*                                                                         *)
(* Scenarios covered:                                                      *)
(*   1. Primed state variables inside operator bodies.                     *)
(*   2. The prime applied to a whole operator application.                 *)
(*   3. Primes combined with LET definitions.                              *)
(*   4. Interaction between formal parameters and state variables.         *)
(*                                                                         *)
(* SANY does not allow a formal parameter to reuse the name of a declared  *)
(* VARIABLE. So scenario 4 passes state variables as arguments to          *)
(* parameters whose role is the same, and checks that a prime on the       *)
(* parameter is not confused with a prime on the state variable.           *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, ok

vars == <<x, y, ok>>

-----------------------------------------------------------------------------
(* Operators under test                                                    *)

\* Body mentions a primed state variable; the parameter is unprimed.
\* A(e) must equal e + x' where x' is the next value of the state variable x.
A(p) == p + x'

\* Prime applied to the formal parameter: B(e) = (e)'.
B(p) == p'

\* No parameters, unprimed body. C' must equal x' + y'.
C == x + y

\* Parameter plus a free state variable. D(e)' must equal (e)' + x'.
D(p) == p + x

\* Parameter used both unprimed and primed. E(e) = e + (e)'.
E(p) == p + p'

\* Parameter plus a primed state variable different from the argument.
\* F(x) must be x + y', not x' + y'.
F(p) == p + y'

\* Nested operator application with a free variable.
G(p) == D(p) + y

-----------------------------------------------------------------------------
(* Individual tests. Each is evaluated in a step where x' and y' have      *)
(* already been determined.                                                *)

\* 1. Priming within operator bodies
T1a == A(y) = y + x'
T1b == A(x) = x + x'
T1c == F(x) = x + y'
T1d == F(y) = y + y'

\* 2. Priming operator applications
T2a == C' = x' + y'
T2b == D(y)' = y' + x'
T2c == D(x)' = x' + x'
T2d == G(y)' = (y' + x') + y'
T2e == B(x) = x'
T2f == B(x + y) = x' + y'
T2g == E(x) = x + x'
T2h == (A(y)') = A(y)' /\ TRUE   \* sanity: prime of constant-level result is fine

\* 3. Priming with LET expressions
T3a == LET z == x IN z' = x'                 \* prime applied to LET-bound name
T3b == LET z == x' IN z = x'                 \* LET captures primed value
T3c == LET z == x IN z + x' = x + x'         \* z stays unprimed
T3d == (LET z == x IN z + y)' = x' + y'      \* prime distributes into LET
T3e == LET z == x' IN z + y = x' + y         \* only x is primed
T3f == LET H(q) == q + y IN H(x)' = x' + y'  \* local operator, primed application
T3g == LET H(q) == q + y' IN H(x) = x + y'   \* local operator with primed body

\* 4. Parameters vs. state variables
\*    Prime on a parameter bound to y must not prime x, and vice versa.
T4a == B(y) = y'
T4b == A(y) # y' + x' \/ y = y'           \* A(y) does not prime its argument
T4c == D(x)' = 2 * x'
T4d == D(y) = y + x                         \* unprimed application stays unprimed

\* 5. Consistency: direct reference vs. operator application
T5a == (x + y)' = C'
T5b == (y + x)' = D(y)'
T5c == x' = B(x)

AllTests ==
    /\ T1a /\ T1b /\ T1c /\ T1d
    /\ T2a /\ T2b /\ T2c /\ T2d /\ T2e /\ T2f /\ T2g /\ T2h
    /\ T3a /\ T3b /\ T3c /\ T3d /\ T3e /\ T3f /\ T3g
    /\ T4a /\ T4b /\ T4c /\ T4d
    /\ T5a /\ T5b /\ T5c

-----------------------------------------------------------------------------
(* State machine                                                           *)

TypeOK ==
    /\ x \in 0..(N - 1)
    /\ y \in 0..(N - 1)
    /\ ok \in BOOLEAN

Init ==
    /\ x = 0
    /\ y = 0
    /\ ok = TRUE

\* Primed variables are assigned first, then the primed expressions are checked.
Step ==
    /\ x' = (x + 1) % N
    /\ y' = x
    /\ ok' = AllTests
    /\ Assert(AllTests, <<"Prime semantics test failed at", x, y>>)

\* A second transition in which y changes independently of x.
Swap ==
    /\ x' = y
    /\ y' = (x + 1) % N
    /\ ok' = AllTests
    /\ Assert(AllTests, <<"Prime semantics test failed (Swap) at", x, y>>)

Next == Step \/ Swap

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Properties                                                              *)

\* Safety: every executed step passed every prime-semantics check.
TestsPass == ok = TRUE

\* Safety: step-level check that every step satisfies the tests.
StepTestsHold == [][AllTests]_vars

\* Liveness: the counter keeps cycling, so the tests are exercised forever.
Progress == []<>(x = 0)

EventuallyNonZero == <>(x # 0)

THEOREM Spec => [](TypeOK /\ TestsPass)
=============================================================================