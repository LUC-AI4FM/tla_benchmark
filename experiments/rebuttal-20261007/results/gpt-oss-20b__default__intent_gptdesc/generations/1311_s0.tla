MODULE GcdSubtraction
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, BMAX

VARIABLES a, b, b0

(* Greatest Common Divisor function *)
Gcd(x,y) ==
  IF y = 0 THEN x
  ELSE Gcd(y, Mod(x,y))

Init ==
  /\ a = A
  /\ b \in 1..BMAX
  /\ b0 = b
  /\ a >= 0
  /\ b >= 0

Next ==
  \/ (* reduce the larger number by the smaller *)
     /\ a > b
     /\ b > 0
     /\ a' = a - b
     /\ b' = b
     /\ b0' = b0
  \/ 
     /\ b > a
     /\ a > 0
     /\ b' = b - a
     /\ a' = a
     /\ b0' = b0
  \/ (* termination: no change *)
     /\ (a = 0 \/ b = 0)
     /\ a' = a
     /\ b' = b
     /\ b0' = b0

vars == <<a,b,b0>>

Inv ==
  /\ a >= 0
  /\ b >= 0
  /\ Gcd(a,b) = Gcd(A, b0)
  /\ a <= Max(A, b0)
  /\ b <= Max(A, b0)

Spec == Init /\ [][Next]_vars

Safety == []Inv

Liveness == []<>(a = 0 \/ b = 0)