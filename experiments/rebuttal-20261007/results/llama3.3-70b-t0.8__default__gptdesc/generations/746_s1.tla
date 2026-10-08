```
MODULE Chameneos
EXTENDS Integers, Naturals

CONSTANTS N, Colors
VARIABLES chamColor, meetCount, meetSlot, totalMeets

Init ==
  /\ chamColor \in [1..Cardinality(Colors)] @@ -> Colors
  /\ meetCount = [i \in 1..Cardinality(Colors) |-> 0]
  /\ meetSlot = nil
  /\ totalMeets = 0

Next ==
  /\ (meetSlot = nil)
    /\ \E c1, c2 \in 1..Cardinality(Colors):
      /\ c1 # c2
      /\ meetSlot' = <<c1, c2>>
      /\ chamColor' = [chamColor EXCEPT ![c1] = Colors \ {chamColor[c1]}, ![c2] = Colors \ {chamColor[c2]}]
      /\ meetCount' = [meetCount EXCEPT ![c1] = meetCount[c1] + 1, ![c2] = meetCount[c2] + 1]
      /\ totalMeets' = totalMeets + 1
  \/ (meetSlot # nil)
    /\ meetSlot' = nil
    /\ chamColor' = chamColor
    /\ meetCount' = meetCount
    /\ totalMeets' = totalMeets
  \/ (totalMeets >= N)
    /\ \E c \in 1..Cardinality(Colors):
      /\ meetSlot' = nil
      /\ chamColor' = [chamColor EXCEPT ![c] = Colors \ {chamColor[c]}]
      /\ meetCount' = meetCount
      /\ totalMeets' = totalMeets

Spec == Init /\ [][Next]_vars
Inv == totalMeets = N => (\* c \in 1..Cardinality(Colors): meetCount[c]) = 2 * N
THEOREM Spec => []Inv
```