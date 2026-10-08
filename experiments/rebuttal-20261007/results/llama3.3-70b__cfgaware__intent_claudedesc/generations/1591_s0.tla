```
MODULE EvenOdd
VARIABLES pc, x, oddCount, evenToOddCount

Even(n) == 
  IF n = 0 THEN TRUE
  ELSE Odd(n - 1)

Odd(n) == 
  IF n = 0 THEN FALSE
  ELSE Even(n - 1)

Init ==
  /\ pc = "Even"
  /\ x = N
  /\ oddCount = 0
  /\ evenToOddCount = 0

Next ==
  IF pc = "Even"
  THEN
    /\ pc' = "Odd"
    /\ x' = x - 1
    /\ oddCount' = oddCount
    /\ evenToOddCount' = evenToOddCount + 1
  ELSE
    /\ pc' = "Even"
    /\ x' = x - 1
    /\ oddCount' = oddCount + 1
    /\ evenToOddCount' = evenToOddCount

Spec == Init /\ [][Next]_<<pc, x, oddCount, evenToOddCount>>

Termination == <>(pc = "Done")

THEOREM Spec => []Termination
THEOREM Spec => [](oddCount = 3 /\ evenToOddCount = 3)

N == 6
```
Note: The `THEOREM` statements are used to specify the properties that should be verified by the model checker. In this case, we verify termination and the expected recursive call pattern for an even input of 6.