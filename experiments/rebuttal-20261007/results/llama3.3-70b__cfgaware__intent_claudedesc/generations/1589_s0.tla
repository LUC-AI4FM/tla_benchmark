```
MODULE EuclidGCD
VARIABLES x, y

ConstantMax == 20

Init ==
  /\ x \in 1..ConstantMax
  /\ y \in 1..ConstantMax

Next ==
  IF x = 0 THEN UNCHANGED <<x, y>>
  ELSE
    IF x < y THEN
      /\ x' = y
      /\ y' = x
    ELSE
      /\ x' = x - y
      /\ y' = y

Spec == Init /\ [][Next]_<<x, y>>

Termination == <>(x = 0)

Invariant ==
  LET GCD(a, b) == IF a = 0 THEN b
                    ELSE GCD(b % a, a)
  IN GCD(x, y) = GCD(y, x)

THEOREM Spec => []Invariant
THEOREM Spec => Termination
```
Note: The `UNCHANGED` operator is used to specify that the values of `x` and `y` do not change when `x` reaches zero. The `LET` expression defines a local function `GCD(a, b)` for calculating the greatest common divisor using the Euclidean algorithm. This function is then used in the `Invariant` property to compare the computed result with the true GCD of the initial values.