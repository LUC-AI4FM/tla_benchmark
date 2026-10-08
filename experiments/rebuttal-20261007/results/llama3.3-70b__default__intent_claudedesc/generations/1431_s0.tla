```
MODULE StateConstraintPitfall
EXTENDS Integers

CONSTANTS MaxLogLength
VARIABLES state, log, done

Init ==
  /\ state = "A"
  /\ log = <<>>
  /\ done = FALSE

Next ==
  /\ IF state = "A" THEN
    /\ state' = "B"
    /\ log' = Append(log, "A")
    /\ done' = done
  ELSE
    /\ state' = "A"
    /\ log' = Append(log, "B")
    /\ done' = done
  /\ IF Len(log) = MaxLogLength THEN
    /\ log' = Tail(log')

Spec ==
  /\ Init
  /\ [][Next]_<<state, log, done>>
  /\ WF_vars(Next, <<state, log, done>>)

StateConstraint ==
  Len(log) <= MaxLogLength

THEOREM Spec => []<>(done = TRUE)
```