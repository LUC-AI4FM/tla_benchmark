---------------------------- MODULE PrimingTest ----------------------------
EXTENDS Naturals

CONSTANTS MaxX

ASSUME MaxX \in Nat

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Operators that do NOT prime their arguments                             *)
(***************************************************************************)
NoPrime(a) == a + 1

UnprimedSum == x + y

Same(a) == a

(***************************************************************************)
(* Operators that DO prime (contain primes)                                *)
(***************************************************************************)
PrimeX == x'

PrimeY == y'

PrimeArg(v) == v'

Bump(v) == v' = v + 1

Keep(v) == v' = v

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ x = 0
    /\ y = 0

(***************************************************************************)
(* Next-state relation exercising priming / variable confusion             *)
(***************************************************************************)
Next ==
    \* Determine x' using an unprimed operator applied to x
    /\ IF x < MaxX
          THEN x' = NoPrime(x)
          ELSE x' = 0
    \* Determine y' via a LET binding of a primed variable
    /\ LET nx == x'
       IN  IF nx > 1
              THEN Keep(y)
              ELSE y' = (y + 1) % 3
    \* Operator that primes internally, used in an IF condition
    /\ IF PrimeX = 0
          THEN TRUE
          ELSE PrimeX > 0
    \* Priming an operator parameter (PrimeArg(x) is x')
    /\ IF PrimeArg(x) = PrimeX
          THEN TRUE
          ELSE FALSE
    \* Priming a LET-defined unprimed expression: s' = x' + y'
    /\ LET s == UnprimedSum
       IN  IF s' = PrimeX + PrimeY
              THEN TRUE
              ELSE FALSE
    \* Priming an unprimed operator directly
    /\ IF (UnprimedSum)' >= 0
          THEN TRUE
          ELSE FALSE
    \* Unprimed operator applied to primed arguments
    /\ IF NoPrime(x') = NoPrime(PrimeX)
          THEN TRUE
          ELSE FALSE
    \* Priming the application of an unprimed operator: (Same(y))' = y'
    /\ IF (Same(y))' = Same(y')
          THEN TRUE
          ELSE FALSE
    \* LET binding mixing primed and unprimed values
    /\ LET old == x
           new == x'
       IN  IF new = 0
              THEN old = MaxX \/ old >= MaxX
              ELSE new = NoPrime(old)
    \* Action operator used within an IF branch (disjunctive choice)
    /\ IF x < MaxX
          THEN Bump(x) \/ x' = NoPrime(x)
          ELSE x' = 0

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

Inv == TRUE

=============================================================================