```
MODULE SimpleCyclicController
EXTENDS Integers, Sequences

CONSTANTS MaxHistoryLength
VARIABLES mode, history, done

Init ==
  /\ mode = "mode1"
  /\ history = << >>
  /\ done = FALSE

Next ==
  IF done THEN
    UNCHANGED <<mode, history, done>>
  ELSE
    (/\ mode = "mode1"
     /\ history' = Append(history, "mode1")
     /\ mode' = "mode2"
     /\ done' = FALSE)
    OR
    (/\ mode = "mode2"
     /\ history' = Append(history, "mode2")
     /\ mode' = "mode1"
     /\ done' = FALSE)
    OR
    (/\ mode' = mode
      /\ history' = history
      /\ done' = (mode = "mode2"))

Spec ==
  Init /\ [][Next]_<<mode, history, done>>

HistoryBoundInvariant ==
  Len(history) < MaxHistoryLength

LivenessProperty ==
  <>done

FairnessConstraint ==
  WF_Vars(Next, <<mode, history, done>>)

THEOREM Spec => []HistoryBoundInvariant
THEOREM Spec => LivenessProperty
THEOREM Spec => FairnessConstraint
```