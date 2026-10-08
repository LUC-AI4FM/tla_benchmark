```
MODULE EuclideanAlgorithm
EXTENDS Integers

CONSTANTS MaxValue
VARIABLES x, y, originalX, originalY

Init ==
  /\ x \in 1..MaxValue
  /\ y \in 1..MaxValue
  /\ originalX = x
  /\ originalY = y

Next ==
  IF x = 0 THEN
    TRUE
  ELSE IF y = 0 THEN
    TRUE
  ELSE IF x > y THEN
    \/ (x' = x - y) /\ (y' = y)
    \/ (x' = y) /\ (y' = x)
  ELSE
    \/ (x' = x) /\ (y' = y - x)
    \/ (x' = y) /\ (y' = x)

Spec == Init /\ [][Next]_<<x, y>>

GCDInvariant ==
  GCD(x, y) = GCD(originalX, originalY)

SwapPreservesCorrectness ==
  IF x > y THEN
    GCD(x - y, y) = GCD(x, y)
  ELSE
    GCD(x, y - x) = GCD(x, y)

PositiveIntegersInvariant ==
  /\ x \in Nat
  /\ y \in Nat

TerminationLiveness == <>[](x = 0 \/ y = 0)

THEOREM Spec => []GCDInvariant
THEOREM Spec => []SwapPreservesCorrectness
THEOREM Spec => []PositiveIntegersInvariant
THEOREM Spec => TerminationLiveness
THEOREM Spec => (x = 0 /\ GCD(originalX, originalY) = y) \/ (y = 0 /\ GCD(originalX, originalY) = x)
```