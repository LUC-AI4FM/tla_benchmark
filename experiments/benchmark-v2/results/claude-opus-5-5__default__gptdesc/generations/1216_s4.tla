---------------------------- MODULE PrimingTest ----------------------------
(***************************************************************************)
(* A test module exploring the subtleties of priming and variable          *)
(* confusion in TLA+.  Several operators either prime or do not prime      *)
(* their arguments.  They are used inside IF-THEN-ELSE and LET-IN          *)
(* expressions in the Next action to exercise how priming interacts with   *)
(* operator application and LET bindings.                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Operators that prime, or do not prime, their arguments.                 *)
(***************************************************************************)
Prime(a)       == a'
NoPrime(a)     == a
PrimeSum(a, b) == a' + b'
Inc(a)         == a + 1
PrimedInc(a)   == (a + 1)'
PrimeIf(c, a, b) == IF c THEN a' ELSE b'

TypeOK == /\ x \in 0..3
          /\ y \in 0..3

Init == /\ x = 0
        /\ y = 0

Next ==
  /\ x' = IF x < 3 THEN x + 1 ELSE 0
  \* LET bindings of primed and unprimed operator applications
  /\ LET px == Prime(x)
         ux == NoPrime(x)
     IN  IF px = ux + 1 \/ (px = 0 /\ ux = 3)
           THEN y' = IF y < 3 THEN y + 1 ELSE 0
           ELSE y' = 0
  \* Priming via operator vs. passing an already primed argument
  /\ IF Prime(x) = NoPrime(x') THEN TRUE ELSE FALSE
  \* Priming an entire operator body vs. applying to a primed argument
  /\ IF PrimedInc(x) = Inc(x') THEN TRUE ELSE FALSE
  \* Priming an unprimed operator application
  /\ IF (NoPrime(x))' = x' THEN TRUE ELSE FALSE
  \* Priming a LET-bound name that is defined as an unprimed variable
  /\ LET z == x
     IN  IF z' = x' THEN TRUE ELSE FALSE
  \* LET-bound name defined as a primed operator application
  /\ LET w == Prime(y)
     IN  IF w = y' THEN TRUE ELSE FALSE
  \* Operator priming multiple arguments
  /\ IF PrimeSum(x, y) = x' + y' THEN TRUE ELSE FALSE
  \* Conditional priming inside an operator
  /\ IF PrimeIf(x < y, x, y) = (IF x < y THEN x' ELSE y')
       THEN TRUE
       ELSE FALSE
  \* Nested IF using both primed and unprimed values
  /\ IF x' = 0
       THEN IF NoPrime(x) = 3 THEN TRUE ELSE FALSE
       ELSE IF Prime(x) = Inc(NoPrime(x)) THEN TRUE ELSE FALSE

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================