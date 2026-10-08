```
MODULE EuclidGCD
VARIABLES x, y, result
CONSTANT N

Spec == 
  /\ x = 24
  /\ y \in 1..N
  /\ result = 0
  /\ WF_Vars({x, y})

Termination == <>[](result # 0)

Next ==
  /\ IF x > y THEN 
    /\ x' = x - y
    /\ y' = y
    /\ result' = result
  ELSE 
    /\ x' = x
    /\ y' = y - x
    /\ result' = result
  /\ IF x = 0 OR y = 0 THEN 
    /\ result' = IF x = 0 THEN y ELSE x

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE GCD(b, a % b)

PrintResult ==
  /\ result # 0
  /\ * Print the result and original second input for verification
  /\ UNCHANGED <<x, y, result>>

Spec == Spec /\ [][Next]_<<x, y, result>> /\ WF_(Next) /\ PrintResult

THEOREM Spec => []Termination
```
Note: The `*` in the `PrintResult` action is a comment and should be replaced with the actual printing statement if TLA+ supports it. However, since TLA+ does not have built-in support for printing, this might need to be handled outside of the TLA+ specification or using a specific model checker's features.

Also note that the `UNCHANGED` operator is used in `PrintResult` to indicate that no change occurs to the variables during the print action. This is necessary because TLA+ requires all actions to specify what happens to every variable, even if it doesn't change.