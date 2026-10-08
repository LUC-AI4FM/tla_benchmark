```
MODULE EuclidGCD
VARIABLES pc, u, v, v_ini

Constant N == 3

GCD(u, v) ==
  IF u = 0 THEN v
  ELSE IF u < v THEN GCD(v, u)
  ELSE GCD(u - v, v)

Init ==
  /\ pc = "lp"
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v

Next ==
  \/ (pc = "lp" /\ u # 0 /\ (u < v => (u' = v /\ v' = u) /\ pc' = "a")
                  /\ ~(u < v => (u' = u /\ v' = v) /\ pc' = "a"))
     /\ (pc' = "lp" /\ u' = u /\ v' = v)
  \/ (pc = "lp" /\ u = 0 /\ PrintGCD /\ pc' = "Done")
  \/ (pc = "a" /\ u' = u - v /\ v' = v /\ pc' = "lp")
  \/ Terminating

PrintGCD == v_ini =<<v>> /\ u = 0

Terminating ==
  pc = "Done" /\ UNCHANGED <<pc, u, v, v_ini>>

Spec == Init /\ [][Next]_<<pc, u, v, v_ini>>
          /\ WF_<<pc, u, v, v_ini>>(Next)

Termination == <>[](pc = "Done")

THEOREM Spec => []Termination
```
Note: The `UNCHANGED` operator is used to specify that the variables do not change in the `Terminating` action. The `WF_` operator is used to specify weak fairness over all variables, ensuring that the algorithm does not stutter indefinitely.