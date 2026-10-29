------------------------------ MODULE PrimeScoping ------------------------------
(***************************************************************************)
(* Test harness for the semantics of the TLA+ prime operator (') when it   *)
(* is applied inside operator definitions, to operator applications, to    *)
(* operators with parameters, to LET-bound names, and to locally defined   *)
(* (possibly nested) LET operators.                                        *)
(*                                                                         *)
(* Each step assigns new values to x and y so that x' # x and y' # y.      *)
(* It then evaluates every test case and records their conjunction in      *)
(* pass. The invariant AllPass requires every test to have evaluated to    *)
(* TRUE in every reachable state.                                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES x, y, pass

vars == <<x, y, pass>>

(***************************************************************************)
(* Operators under test                                                    *)
(***************************************************************************)
PrimeInside == x'            \* prime appears inside the operator body
SumXY       == x + y         \* body has only unprimed state variables
Inc(a)      == a + 1         \* depends only on its parameter
AddX(a)     == a + x         \* combines a parameter with a state variable
MulX(a)     == a * x         \* combines a parameter with a state variable
K           == 5             \* constant-level operator (priming is a no-op)

(***************************************************************************)
(* 1. Priming inside operator definitions                                  *)
(***************************************************************************)
T1a == PrimeInside = x'
T1b == PrimeInside = x + 1
T1c == PrimeInside # x

(***************************************************************************)
(* 2. Priming an entire operator application                               *)
(***************************************************************************)
T2a == (SumXY)' = x' + y'
T2b == (SumXY)' # SumXY
T2c == SumXY = x + y

(***************************************************************************)
(* 3. Priming an application with a variable argument versus priming the   *)
(*    argument before it is passed                                         *)
(***************************************************************************)
T3a == Inc(x)' = Inc(x')                 \* identical: body has no state vars
T3b == AddX(x)' = x' + x'                \* both occurrences become primed
T3c == AddX(x') = x' + x                 \* only the argument is primed
T3d == AddX(x)' # AddX(x')               \* the two forms differ when x' # x

(***************************************************************************)
(* 4. Priming LET-bound names                                              *)
(***************************************************************************)
T4a == LET z == x + y IN z' = x' + y'
T4b == LET z == x IN z' # z
T4c == LET z == x IN (z' = x') /\ (z = x)
T4d == LET z == x + y IN z' = (x + y)'

(***************************************************************************)
(* 5. Priming applications that combine state variables with parameters    *)
(*    (priming affects state variables, not constant parameter values)     *)
(***************************************************************************)
T5a == MulX(K)' = K * x'
T5b == LET p == 3 IN AddX(p)' = x' + 3
T5c == AddX(y)' = y' + x'
T5d == AddX(7)' = x' + 7

(***************************************************************************)
(* 6. Nested LET with locally defined operators                            *)
(***************************************************************************)
T6a == LET L(a) == a * x IN L(2)' = 2 * x'
T6b == LET L(a) == LET w == a + y IN w * x
       IN  L(1)' = (1 + y') * x'
T6c == LET L(a) == a + x
       IN  LET M(b) == L(b) * 2
           IN  M(y)' = (y' + x') * 2
T6d == LET L(a) == a + x' IN L(x) = x + x'
T6e == LET L(a) == a + x
       IN  LET v == L(y)
           IN  (v' = y' + x') /\ (v = y + x)

AllTests ==
    /\ T1a /\ T1b /\ T1c
    /\ T2a /\ T2b /\ T2c
    /\ T3a /\ T3b /\ T3c /\ T3d
    /\ T4a /\ T4b /\ T4c /\ T4d
    /\ T5a /\ T5b /\ T5c /\ T5d
    /\ T6a /\ T6b /\ T6c /\ T6d /\ T6e

(***************************************************************************)
(* Behavior                                                                *)
(***************************************************************************)
Init ==
    /\ x = 0
    /\ y = 0
    /\ pass = TRUE

Step ==
    /\ x < N
    /\ x' = x + 1
    /\ y' = y + x + 1
    /\ pass' = (pass /\ AllTests)

Done ==
    /\ x = N
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ x \in 0..N
    /\ y \in Nat
    /\ pass \in BOOLEAN

AllPass == pass = TRUE

\* Every executed step must satisfy all prime-semantics tests.
StepTestsHold == [][Step => AllTests]_vars

\* The harness eventually completes all steps.
Termination == <>(x = N)

\* Upon completion, all validations have passed.
CompletesSuccessfully == <>[](x = N /\ pass = TRUE)

THEOREM Spec => []TypeOK /\ []AllPass /\ StepTestsHold /\ Termination
=============================================================================