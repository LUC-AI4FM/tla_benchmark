------------------------------ MODULE EuclidSubtraction ------------------------------
EXTENDS Integers

CONSTANTS A, DOMAIN

VARIABLES a, b, b0

(* Helper function: maximum of two naturals *)
Max(a,b) == IF a >= b THEN a ELSE b

(* Recursive GCD function using modulo *)
GCD(x,y) ==
  IF y = 0 THEN x
  ELSE GCD(y, Mod(x,y))

Init ==
  /\ a = A
  /\ b0 \in DOMAIN
  /\ b = b0
  /\ a >= 1
  /\ b >= 1

Terminate == (a = 0 \/ b = 0)

Next ==
  \/ (a > b) /\ a' = a - b /\ b' = b /\ b0' = b0
  \/ (b > a) /\ a' = a /\ b' = b - a /\ b0' = b0
  \/ Terminate /\ a' = a /\ b' = b /\ b0' = b0

GcdInvariant == GCD(a,b) = GCD(A,b0)

Safety ==
  /\ a >= 0
  /\ b >= 0
  /\ a <= Max(A, b0)
  /\ b <= Max(A, b0)

Spec == Init /\ [][Next]_<<a,b,b0>>

THEOREM GcdInvariantIsMaintained
  Spec => []GcdInvariant

THEOREM SafetyIsMaintained
  Spec => []Safety

THEOREM TerminationLiveness
  Spec => <>Terminate

=============================================================================