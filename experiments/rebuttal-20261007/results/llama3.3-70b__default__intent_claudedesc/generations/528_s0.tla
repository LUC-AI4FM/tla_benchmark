```
MODULE SimplePlusCalExample
EXTENDS Integers, Sequences, TLC

CONSTANTS

VARIABLES 
  setVar,
  seqVar,
  done

Init ==
  /\ setVar = {"a", "b"}
  /\ seqVar = <<1, 2, 3>>
  /\ done = FALSE

Next ==
  IF ~done THEN
    /\ setVar' = setVar \cup {"c"}
    /\ seqVar' = [seqVar EXCEPT ![2] = 4]
    /\ done' = (setVar = setVar' /\ seqVar = seqVar')
    /\ Print("Set after adding 'c': ", setVar')
    /\ Print("Sequence after updating second element: ", seqVar')
  ELSE
    /\ setVar' = setVar
    /\ seqVar' = seqVar
    /\ done' = TRUE

Spec ==
  Init /\ [][Next]_<<setVar, seqVar, done>>

THEOREM Spec => []~(done') 
```