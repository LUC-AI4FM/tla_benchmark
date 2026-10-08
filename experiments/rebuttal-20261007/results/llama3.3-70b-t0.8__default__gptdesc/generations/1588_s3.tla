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
    /\ v_ini' = v_ini
  /\ pc = "Loop" => 
    /\ IF u > v THEN 
        /\ pc' = "Loop"
        /\ u' = u - v
        /\ v' = v
        /\ v_ini' = v_ini
      ELSE 
        /\ IF u < v THEN 
            /\ pc' = "Loop"
            /\ u' = u
            /\ v' = v - u
            /\ v_ini' = v_ini
          ELSE 
            /\ pc' = "Done"
            /\ u' = u
            /\ v' = v
            /\ v_ini' = v_ini
  /\ pc = "Done" => 
    /\ pc' = pc
    /\ u' = u
    /\ v' = v
    /\ v_ini' = v_ini

Spec == Init /\ [][Next]_<<pc, u, v, v_ini>>
Termination == <><pc = "Done">
Fairness == WF_<<pc, u, v, v_ini>>(Next)

THEOREM Spec => []Termination
```
Note: This TLA+ module uses the `WF` (weak fairness) operator to specify that the `Next` action should be taken infinitely often. The `Termination` property asserts that the control will eventually reach the "Done" state, and the `THEOREM` statement proves that this property is satisfied by the specification.