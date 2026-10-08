------------------------------ MODULE EuclidSpec ------------------------------
EXTENDS Integers, Temporal

CONSTANT N

VARIABLES x, y, origY, finished, result, output

vars == <<x,y,origY,finished,result,output>>

(* Mathematical GCD *)
RECURSIVE Gcd/2
DEFINE
  Gcd(a,b) == IF b = 0 THEN a ELSE Gcd(b, a % b)

Init ==
  /\ x = 24
  /\ y \in 1..N
  /\ origY = y
  /\ finished = FALSE
  /\ result = 0
  /\ output = <<>>

Subtract ==
  \/ (x > y) /\ x' = x - y /\ y' = y
  \/ (y > x) /\ y' = y - x /\ x' = x
  \/ (x = y /\ x > 0) /\ y' = 0 /\ x' = x
  /\ UNCHANGED <<origY, finished, result, output>>

Finish ==
  /\ (x = 0 \/ y = 0)
  /\ NOT finished
  /\ finished' = TRUE
  /\ result' = IF x = 0 THEN y ELSE x
  /\ output' = <<origY, result'>>
  /\ UNCHANGED <<x,y,origY>>

Next == Subtract \/ Finish

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Subtract)

SafetyInvariant ==
  finished => result = Gcd(24, origY)

Termination ==
  <> (finished)

Liveness == Termination
=============================================================================