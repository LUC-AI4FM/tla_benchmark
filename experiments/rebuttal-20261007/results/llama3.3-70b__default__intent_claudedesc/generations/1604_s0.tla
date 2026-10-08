```
MODULE ProceduralComposition
EXTENDS Integers, Strings

CONSTANTS 

VARIABLES 
  x, y, result, output, pc

Init ==
  (pc = "Start") /\ (x = 3) /\ (y = 7) /\ (result = 0) /\ (output = "")

Add(a, b) ==
  result := a + b
  pc := "Added"

Convert(n) ==
  IF n = 10 THEN
    output := "10"
    pc := "Converted"
  ELSE
    pc := "Error"

Next ==
  IF pc = "Start" THEN
    Add(x, y)
  ELSE IF pc = "Added" THEN
    Convert(result)
  ELSE IF pc = "Converted" THEN
    TRUE

Spec ==
  Init /\ [][Next]_<<x, y, result, output, pc>>

THEOREM Spec => []<>(pc = "Converted" /\ output = "10")
```