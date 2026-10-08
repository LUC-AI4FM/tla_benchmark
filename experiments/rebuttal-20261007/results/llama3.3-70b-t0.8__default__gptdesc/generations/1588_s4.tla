```
MODULE Euclid
EXTENDS Integers

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v_ini \in 1..N
  /\ v = v_ini

Next ==
  /\ pc = "Start" => 
    /\ pc' = "Loop"
    /\ u' = u
    /\ v' = v
  /\ pc = "Loop" =>
    /\ IF u > v
        THEN /\ pc' = "Loop"
             /\ u' = u - v
             /\ v' = v
        ELSE /\ IF v > u
                 THEN /\ pc' = "Loop"
                      /\ u' = u
                      /\ v' = v - u
                 ELSE /\ pc' = "Done"
                      /\ u' = u
                      /\ v' = v
  /\ pc = "Done" => 
    /\ pc' = pc
    /\ u' = u
    /\ v' = v

Spec == Init /\ [][Next]_<<pc, u, v>>

Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```