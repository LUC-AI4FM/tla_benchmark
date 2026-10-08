------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Max
ASSUME Max = 20

VARIABLES x, y, initX, initY

Init ==
  /\ initX \in 1..Max
  /\ initY \in 1..Max
  /\ x = initX
  /\ y = initY

Next ==
  IF x > 0 THEN
    IF x <= y THEN
      /\ x' = y - x
      /\ y' = x
    ELSE
      /\ x' = x - y
      /\ y' = y
  ELSE
    UNCHANGED <<x, y, initX, initY>>

Termination == (x = 0)

GCD(a,b) ==
  LET m == IF a <= b THEN a ELSE b
      candidates == {d \in 1..m : a % d = 0 /\ b % d = 0}
  IN MAX(candidates)

Invariant ==
  /\ x >= 0
  /\ y > 0
  /\ Termination => (y = GCD(initX, initY))

Spec == Init /\ [][Next]_<<x,y,initX,initY>>

THEOREM SafetyHolds ==
  Spec => []Invariant

THEOREM LivenessHolds ==
  Spec => []<>(Termination)

============================================================================