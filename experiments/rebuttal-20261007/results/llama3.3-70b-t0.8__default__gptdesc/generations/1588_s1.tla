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
Termination == <>[]pc = "Done"
Fairness == WF_<<pc, u, v, v_ini>>(Next)

THEOREM Spec => []Termination
```
Note: The `WF_` (weak fairness) operator and the `<>[]` (eventually always) temporal operators are used to express the weak fairness of `Next` and the termination property respectively.