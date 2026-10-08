```
MODULE EuclidAlgorithm
EXTENDS Integers

CONSTANTS N
VARIABLES pc, u, v, v_ini

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v_ini \in 1..N
  /\ v = v_ini

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "Loop"
    /\ u' = u
    /\ v' = v
  /\ (pc = "Loop") =>
    /\ IF u > v THEN
        /\ pc' = "Loop"
        /\ u' = u - v
        /\ v' = v
      ELSE
        /\ pc' = "Swap"
        /\ u' = v
        /\ v' = u
    /\ (pc = "Swap") =>
      /\ IF v > 0 THEN
          /\ pc' = "Loop"
          /\ u' = u
          /\ v' = v - u
        ELSE
          /\ pc' = "Done"
          /\ u' = u
          /\ v' = v

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u, v>>
  /\ WF_<<pc, u, v>>(Next)

Termination ==
  <>(pc = "Done")
```
Note: This TLA+ module assumes that the SANY parser and TLC (TLA+ model checker) are used for parsing and checking the specification.