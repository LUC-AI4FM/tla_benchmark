```tla
MODULE EuclidAlgorithm

EXTENDS Integers, TLC

CONSTANTS MaxNum

VARIABLES pc, u, v, u_ini, v_ini

Init == 
  (pc = "a") /\ 
  (u \in 1..MaxNum) /\ 
  (v \in 1..MaxNum) /\ 
  (u_ini = u) /\ 
  (v_ini = v)

GCD(x, y) == 
  LET Divisors == {d \in 1..x : x % d = 0} 
  IN CHOOSE z \in Divisors : \A d \in Divisors : (y % d = 0 => z % d = 0)

Next == 
  IF pc = "a" THEN 
    IF u # 0 THEN 
      IF u < v THEN 
        (pc' = "b") /\ (u' = v) /\ (v' = u) /\ (u_ini' = u_ini) /\ (v_ini' = v_ini)
      ELSE 
        (pc' = "b") /\ (u' = u - v) /\ (v' = v) /\ (u_ini' = u_ini) /\ (v_ini' = v_ini)
    ELSE 
      (pc' = "Done") /\ (u' = u) /\ (v' = v) /\ (u_ini' = u_ini) /\ (v_ini' = v_ini) /\ (v = GCD(u_ini, v_ini))
  ELSE 
    (pc' = pc) /\ (u' = u) /\ (v' = v) /\ (u_ini' = u_ini) /\ (v_ini' = v_ini)

Termination == <>[] (pc = "Done")

Invariant == 
  [] ((pc = "Done") => (v = GCD(u_ini, v_ini)))

Spec == Init /\ [][Next]_<<pc, u, v, u_ini, v_ini>> /\ WF_<<pc, u, v, u_ini, v_ini>>(Next)

THEOREM Spec => []Termination

POSTCONDITION PossibleCounts == 
  (TLC.numStates = 800) /\ (TLC.numTransitions = 698)
```