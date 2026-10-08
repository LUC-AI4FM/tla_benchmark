------------------------------ MODULE EuclidSpec ------------------------------
EXTENDS Integers

CONSTANT N

VARIABLES a, b, b0

(* Mathematical GCD function *)
RECURSIVE EuclidGcd(_,_)

EuclidGcd(x,y) == IF x = 0 THEN y ELSE EuclidGcd(y % x, x)

Init ==
  /\ b0 \in 1 .. N
  /\ a = 24
  /\ b = b0

Next ==
  /\ a > 0 /\ b > 0
  /\ IF a >= b THEN
       a' = a - b /\ b' = b
     ELSE
       a' = a /\ b' = b - a
  /\ b0' = b0

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination ==
  [] ((a > 0 /\ b > 0) => <> (a = 0 \/ b = 0))

Correct ==
  [] ((a = 0 \/ b = 0) =>
        IF a = 0 THEN b ELSE a = EuclidGcd(24, b0))

============================================================================