```
MODULE Chameneos
EXTENDS Integers, TLC

CONSTANTS Colors, N
VARIABLES chamColor, meetCount, slot, totalMeets

Init ==
  /\ chamColor \in [1..Cardinality(Colors)] -> Colors
  /\ meetCount = [i \in 1..Cardinality(Colors) |-> 0]
  /\ slot = NULL
  /\ totalMeets = 0

Next ==
  \/ \E c \in 1..Cardinality(Colors):
      /\ slot = NULL
      /\ chamColor[c] /= Colors[SlotEmpty]
      /\ meetCount' = [meetCount EXCEPT ![c] = meetCount[c] + 1]
      /\ slot' = c
      /\ totalMeets' = totalMeets + 1
      /\ chamColor' = [chamColor EXCEPT ![c] = GetComplement(chamColor[c])]
  \/ \E c \in 1..Cardinality(Colors):
      /\ slot = c
      /\ meetCount' = meetCount
      /\ slot' = NULL
      /\ totalMeets' = totalMeets
      /\ chamColor' = [chamColor EXCEPT ![c] = GetComplement(chamColor[c])]
  \/ \E c \in 1..Cardinality(Colors):
      /\ slot = NULL
      /\ totalMeets >= N
      /\ meetCount' = meetCount
      /\ slot' = NULL
      /\ totalMeets' = totalMeets
      /\ chamColor' = [chamColor EXCEPT ![c] = Colors[Faded]]

Spec == Init /\ [][Next]_vars

GetComplement(color) ==
  IF color = "red" THEN "blue"
  ELSE IF color = "blue" THEN "green"
  ELSE "red"

THEOREM Spec => []((totalMeets = N) => (\A c \in 1..Cardinality(Colors): meetCount[c] = 2 * N))
```