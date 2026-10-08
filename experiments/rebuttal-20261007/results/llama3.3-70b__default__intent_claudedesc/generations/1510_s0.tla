```
MODULE CaseRecordUpdate
EXTENDS Integers

CONSTANTS ValueSet, SpecificValue, DesignatedConstant
VARIABLES variable, function

Init ==
  /\ variable \in ValueSet
  /\ function = [i \in ValueSet |-> 0]

Next ==
  /\ variable' = variable
  /\ function' = 
    CASE variable = SpecificValue -> 
      [function EXCEPT ![SpecificValue] = DesignatedConstant]
    OTHER -> function

Spec == Init /\ [][Next]_<<variable, function>>
```
THEOREM Spec => []Init