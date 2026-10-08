MODULE EuclidGCD
EXTENDS Naturals, Integers

CONSTANT Max

VARIABLES a, b

Init ==
  /\ a = 24
  /\ b ∈ 1..Max

Next ==
  /\ a # 0
  /\ (a' = IF a < b THEN b - a ELSE a - b)
  /\ (b' = IF a < b THEN a ELSE b)

Inv ==
  /\ a >= 0
  /\ b > 0

Spec == Init /\ [][Next]_<<a,b>> /\ Inv

===============================================================================