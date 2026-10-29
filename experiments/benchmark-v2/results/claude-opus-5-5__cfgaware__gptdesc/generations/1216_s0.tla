---------------------------- MODULE PrimingTest ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Operator that primes its argument
Prime(e) == e'

\* Operator that does not prime its argument
NoPrime(e) == e

\* Operator that compares a primed argument against an unprimed one
Changed(e) == e' # e

\* Operator that mixes primed and unprimed occurrences
Succ(e) == e' = e + 1

Init ==
  /\ x = 0
  /\ y = 0

Next ==
  \* Determine x' first so later conjuncts can refer to it
  /\ IF x < 3 THEN x' = x + 1 ELSE x' = 0
  \* Prime applied through an operator: Prime(x) is x'
  /\ IF Prime(x) = 0 THEN y' = 1 - y ELSE y' = y
  \* LET-bound name for a primed expression
  /\ LET z == x'
     IN  IF z = NoPrime(x) + 1 THEN TRUE ELSE z = 0
  \* LET-bound name for an unprimed expression, then primed outside
  /\ LET w == x
     IN  IF w' = Prime(x) THEN TRUE ELSE FALSE
  \* Priming an operator application that does not prime its argument
  /\ IF NoPrime(y)' = y' THEN TRUE ELSE FALSE
  \* Priming a compound expression via an operator
  /\ IF Prime(x + y) = x' + y' THEN TRUE ELSE FALSE
  \* Operators that mix primed/unprimed occurrences inside IF
  /\ IF x < 3 THEN Succ(x) ELSE ~Succ(x)
  /\ IF Changed(x) THEN TRUE ELSE x' = x
  \* Nested IF with LET and NoPrime of a primed expression
  /\ LET a == NoPrime(x')
         b == NoPrime(x)'
     IN  IF a = b THEN TRUE ELSE FALSE

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================