---------------------------- MODULE PrimingTest ----------------------------
(***************************************************************************)
(* A test module exploring the subtleties of priming and variable          *)
(* confusion in TLA+.  Several operators either prime or do not prime     *)
(* their arguments.  They are used in IF-THEN-ELSE expressions and        *)
(* LET-IN bindings inside Next to exercise how priming interacts with     *)
(* operator application.                                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Operators that do NOT prime their arguments.                           *)
(***************************************************************************)
NoPrime(a) == a + 1

Same(a) == a

NotPrimeX == x

NotPrimeY == y

(***************************************************************************)
(* Operators that DO prime their arguments (or variables).                *)
(***************************************************************************)
PrimeArg(a) == a'

PrimeX == x'

PrimeY == y'

PrimedSum(a, b) == a' + b'

(***************************************************************************)
(* Action-level helper operators.                                         *)
(***************************************************************************)
IncX == x' = (x + 1) % 4

KeepY == y' = y

-----------------------------------------------------------------------------

TypeOK == /\ x \in 0..3
          /\ y \in 0..1

Init == /\ x = 0
        /\ y = 0

(***************************************************************************)
(* Step A: unprimed operator in the IF condition, primed operator applied *)
(* to an unprimed variable in a later conjunct (refers to the new x).     *)
(***************************************************************************)
StepA ==
    /\ x < 3
    /\ IF NoPrime(x) > 2 THEN x' = 0 ELSE x' = NoPrime(x)
    /\ y' = IF PrimeArg(x) = 0 THEN 1 ELSE 0

(***************************************************************************)
(* Step B: LET bindings, one unprimed and one primed, compared inside IF. *)
(***************************************************************************)
StepB ==
    /\ x >= 3
    /\ x' = 0
    /\ LET a == NotPrimeX
           b == PrimeX
       IN  y' = IF b = a THEN y ELSE 1 - y

(***************************************************************************)
(* Step C: priming an operator application (NotPrimeX' is x'), and        *)
(* priming a non-priming operator applied to a variable (NoPrime(y)' is   *)
(* y' + 1).                                                               *)
(***************************************************************************)
StepC ==
    LET c == NoPrime(y)
    IN  /\ IF c > 1 THEN UNCHANGED x ELSE IncX
        /\ y' = IF NotPrimeX' = x THEN y ELSE (c % 2)
        /\ NoPrime(y)' = PrimeY + 1

(***************************************************************************)
(* Step D: IF condition that itself contains primes, with Same applied    *)
(* both to primed and unprimed expressions, and a primed operator taking  *)
(* two arguments.                                                         *)
(***************************************************************************)
StepD ==
    /\ IncX
    /\ IF PrimeX > Same(x)
          THEN y' = IF Same(x') = Same(x) + 1 THEN 1 - y ELSE y
          ELSE KeepY
    /\ PrimedSum(x, y) = Same(x') + Same(y')

(***************************************************************************)
(* Step E: nested LET where an inner binding primes an outer binding.     *)
(***************************************************************************)
StepE ==
    LET u == NotPrimeY
    IN  LET v == PrimeArg(u)
        IN  /\ y' = 1 - y
            /\ UNCHANGED x
            /\ IF v = u THEN FALSE ELSE TRUE

Next == StepA \/ StepB \/ StepC \/ StepD \/ StepE

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Inv == TRUE

THEOREM Spec => [](TypeOK /\ Inv)

=============================================================================