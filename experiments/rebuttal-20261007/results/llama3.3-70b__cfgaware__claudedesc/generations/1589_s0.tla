---------------------------- MODULE Euclid --------------------------------
EXTENDS Integers

CONSTANT MaxNum

VARIABLE pc, u, v, u_ini, v_ini

GCD(x, y) == CHOOSE z : z \in (1..x) /\ z \in (1..y) /\ 
             \A w \in (1..x) /\ w \in (1..y) : w <= z

Init ==
  /\ pc = "a"
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini

Next ==
  \/ (pc = "a" /\ u # 0 /\ 
      IF u < v THEN /\ pc' = "b" /\ u' = v /\ v' = u
                 ELSE /\ pc' = "b" /\ u' = u - v /\ v' = v
      )
     \/ (pc = "a" /\ u = 0 /\ pc' = "Done" /\ v' = v)
     \/ (pc = "b" /\ pc' = "a" /\ u' = u - v /\ v' = v)

Spec == Init /\ [][Next]_<<pc, u, v, u_ini, v_ini>> 
           /\ WF_<<pc, u, v, u_ini, v_ini>>(Next)

Termination == <>[]pc = "Done"

Invariant == []((pc = "Done") => (v = GCD(u_ini, v_ini)))

THEOREM Spec => []Invariant
=============================================================================