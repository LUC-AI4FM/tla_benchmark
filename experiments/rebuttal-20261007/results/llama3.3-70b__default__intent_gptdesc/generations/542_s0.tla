```
MODULE IncrementWorkers
EXTENDS Integers

CONSTANTS Worker1Enabled, Worker2Enabled
VARIABLES counter, worker1Finished, worker2Finished

Init ==
  /\ counter = 0
  /\ worker1Finished = FALSE
  /\ worker2Finished = FALSE

Next ==
  \/ (worker1Finished' = TRUE
      /\ worker2Finished' = worker2Finished
      /\ counter' = counter + 1)
  \/ (worker2Finished' = TRUE
      /\ worker1Finished' = worker1Finished
      /\ counter' = counter + 1)
  \/ (* idle *)
     (worker1Finished' = worker1Finished
      /\ worker2Finished' = worker2Finished
      /\ counter' = counter)

Spec ==
  Init /\ [][Next]_<<counter, worker1Finished, worker2Finished>>
  /\ WF_vars(Worker1Enabled, <<counter, worker1Finished, worker2Finished>>)
  /\ WF_vars(Worker2Enabled, <<counter, worker1Finished, worker2Finished>>)

THEOREM Spec => []<>(worker1Finished /\ worker2Finished)
THEOREM Spec => <>[](counter = 2)
```
Note: The `WF_vars` fairness condition is used to ensure that each worker will eventually execute its increment if it is continuously enabled. This corresponds to the weak fairness assumption mentioned in the problem description.

Also, note that this specification does not explicitly define the `Worker1Enabled` and `Worker2Enabled` constants, as they are assumed to be defined elsewhere (e.g., in a separate module or as part of a larger system). In practice, these constants would need to be defined in order for the specification to be complete. 

However, based on the description provided, we can assume that `Worker1Enabled` and `Worker2Enabled` are always true when their respective workers are not finished, which is implicitly captured by the `Next` action.