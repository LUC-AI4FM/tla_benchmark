```
MODULE Counter
EXTENDS Integers

CONSTANTS None

VARIABLES counter, reached2, reached1, wrapped

Init ==
  /\ counter = 0
  /\ reached2 = FALSE
  /\ reached1 = FALSE
  /\ wrapped = FALSE

Next ==
  /\ counter' = (counter + 1) % 3
  /\ IF counter = 2 THEN wrapped' = TRUE ELSE wrapped' = wrapped
  /\ IF counter = 2 THEN reached2' = TRUE ELSE reached2' = reached2
  /\ IF counter = 1 THEN reached1' = TRUE ELSE reached1' = reached1

Spec ==
  Init /\ [][Next]_counter

THEOREM Spec => <>reached2
THEOREM Spec => <>reached1
THEOREM Spec => <>wrapped

POSSIBLE == 
  /\ _possible(reached2)
  /\ _possible(reached1)
  /\ _possible(wrapped)

Postcondition ==
  /\ _num_witnesses(reached2) = 1
  /\ _num_witnesses(reached1) = 1
  /\ _num_witnesses(wrapped) = 1

THEOREM Spec => []<>POSSIBLE
```
Note: The `_POSSIBLE` directive and related functions like `_possible`, `_num_witnesses` are not standard TLA+ but rather an extension used for demonstration purposes in this context. In actual TLA+ specifications, you would typically use standard temporal logic operators to express such properties.