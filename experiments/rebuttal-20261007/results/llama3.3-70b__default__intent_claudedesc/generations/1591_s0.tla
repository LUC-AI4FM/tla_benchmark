```
MODULE EvenOdd
EXTENDS Integers

CONSTANTS N

VARIABLES pc, x, result, oddCount, evenToOddCount

Init ==
  /\ pc = "Even"
  /\ x = N
  /\ result = FALSE
  /\ oddCount = 0
  /\ evenToOddCount = 0

Next ==
  IF pc = "Even" THEN
    /\ IF x = 0 THEN
        /\ pc' = "Done"
        /\ result' = TRUE
        /\ oddCount' = oddCount
        /\ evenToOddCount' = evenToOddCount
      ELSE
        /\ pc' = "Odd"
        /\ x' = x - 1
        /\ result' = result
        /\ oddCount' = oddCount
        /\ evenToOddCount' = evenToOddCount + 1
    /\ IF x # 0 THEN
        /\ UNCHANGED result
      ELSE
        /\ UNCHANGED oddCount
        /\ UNCHANGED evenToOddCount
  ELSE IF pc = "Odd" THEN
    /\ IF x = 0 THEN
        /\ pc' = "Done"
        /\ result' = FALSE
        /\ oddCount' = oddCount + 1
        /\ evenToOddCount' = evenToOddCount
      ELSE
        /\ pc' = "Even"
        /\ x' = x - 1
        /\ result' = result
        /\ oddCount' = oddCount + 1
        /\ evenToOddCount' = evenToOddCount
    /\ IF x # 0 THEN
        /\ UNCHANGED result
      ELSE
        /\ UNCHANGED evenToOddCount
  ELSE
    /\ UNCHANGED pc
    /\ UNCHANGED x
    /\ UNCHANGED result
    /\ UNCHANGED oddCount
    /\ UNCHANGED evenToOddCount

Spec == Init /\ [][Next]_<<pc, x, result, oddCount, evenToOddCount>>
Termination == <>(pc = "Done")
EvenToOddExactly3Times == []<>(evenToOddCount = 3)
OddEnteredExactly3Times == []<>(oddCount = 3)

THEOREM Spec => Termination
THEOREM Spec => EvenToOddExactly3Times
THEOREM Spec => OddEnteredExactly3Times

ASSUME N = 6
```