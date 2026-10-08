```tla
MODULE EuclidGCD
EXTENDS Integers

CONSTANTS N
VARIABLES x, y, result, done

Init == 
  /\ x = 24
  /\ y \in 1..N
  /\ result = 0
  /\ done = FALSE

Next == 
  IF done THEN 
    UNCHANGED <<x, y, result, done>>
  ELSE 
    IF x = 0 THEN 
      /\ result := y
      /\ done := TRUE
    ELSE IF y = 0 THEN 
      /\ result := x
      /\ done := TRUE
    ELSE IF x > y THEN 
      /\ x := x - y
      /\ UNCHANGED <<y, result, done>>
    ELSE 
      /\ y := y - x
      /\ UNCHANGED <<x, result, done>>

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE IF a > b THEN GCD(a - b, b)
  ELSE GCD(a, b - a)

Spec == Init /\ [][Next]_<<x, y, result, done>>
Termination == <><done>
Correctness == []<>(done => result = GCD(24, y))
WF_Next == []<><Next>_<<x, y, result, done>>

THEOREM Termination => []<>Termination
THEOREM Spec => Correctness

```
Note: The `THEOREM` statements are used to specify the properties that should be verified by the model checker. In this case, we verify termination and correctness of the algorithm.