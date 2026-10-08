```
MODULE BooleanClock
VARIABLE clock

Init == clock = TRUE

Next == clock' = ~clock

TypeOK == clock \in {TRUE, FALSE}

THEOREM Spec => []TypeOK
  SPECIFICATION Spec == Init /\ [][Next]_clock
```

Note: The `Spec` theorem is used to define the overall specification and check that it implies the type invariant `TypeOK` always holds. This allows TLC to model-check the correctness property of interest, which is that the clock remains a boolean value throughout all possible behaviors of the system.