```
MODULE Spec
VARIABLES setVar, seqVar, done

Init ==
  /\ setVar = {"a", "b"}
  /\ seqVar = <<1, 2, 3>>
  /\ done = FALSE

AddToSet ==
  /\ setVar' = setVar \cup {"c"}
  /\ seqVar' = seqVar
  /\ done' = FALSE

UpdateSequence ==
  /\ setVar' = setVar
  /\ seqVar' = [seqVar EXCEPT ![2] = 5]
  /\ done' = TRUE

PrintSet ==
  PrintTLA("Set after adding element: ", setVar)

PrintSequence ==
  PrintTLA("Sequence after updating element: ", seqVar)

Next ==
  IF ~done THEN
    /\ AddToSet
    /\ PrintSet
    /\ UpdateSequence
    /\ PrintSequence
  ELSE
    /\ setVar' = setVar
    /\ seqVar' = seqVar
    /\ done' = done

Spec ==
  Init /\ [][Next]_<<setVar, seqVar, done>>
```
Note: The `PrintTLA` operator is not a standard TLA+ operator. It's used here to simulate printing the values of variables for demonstration purposes. In a real-world specification, you would typically use TLC's model checking features to verify properties rather than print intermediate results.