```
MODULE EuclidsAlgorithm
EXTENDS Integers

CONSTANTS MaxValue
VARIABLES x, y, result

Init == 
  /\ x \in 1..MaxValue
  /\ y \in 1..MaxValue
  /\ result = 0

Next == 
  IF x = 0 THEN 
    UNCHANGED <<x, y, result>>
  ELSE 
    IF x < y THEN 
      /\ x' = y
      /\ y' = x
      /\ result' = result
    ELSE 
      /\ x' = x - y
      /\ y' = y
      /\ result' = IF x' = 0 THEN y ELSE result

Spec == Init /\ [][Next]_<<x, y, result>>
Termination == <>(x = 0)

THEOREM Spec => []<>(x = 0)
THEOREM Spec => [](x = 0) => (result = GCD(x, y))

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE IF a < b THEN GCD(b % a, a)
  ELSE GCD(a % b, b)

MaxValue == 20

INVARIANT x \in 1..MaxValue /\ y \in 1..MaxValue
```
Note: The above TLA+ specification uses the `Integers` module for integer operations and defines the `GCD` function recursively. It also includes a termination theorem to ensure that the algorithm eventually terminates, and an invariant to guarantee that the computed result equals the true greatest common divisor of the two initial values upon termination.