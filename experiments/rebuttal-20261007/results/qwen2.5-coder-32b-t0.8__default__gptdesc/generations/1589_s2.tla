------------------------------- MODULE EuclidsGCD ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

Init == /\ pc = "start"
        /\ u \in 1..MaxNum
        /\ v \in 1..MaxNum
        /\ u_ini = u
        /\ v_ini = v

Next ==
    \/ /\ pc = "start"
       /\ \/ /\ u > v
              /\ u' = u - v
              /\ v' = v
          \/ /\ u <= v
             /\ u' = u
             /\ v' = v - u
       /\ pc' = "start"
    \/ /\ pc = "start"
       /\ u = v
       /\ pc' = "done"

Spec == Init /\ [][Next]_<<pc, u, v>>

GCD(x, y) ==
  LET Recur(a, b) ==
      IF a = b THEN a
      ELSE IF a > b THEN Recur(a - b, b)
           ELSE Recur(a, b - a)
  IN  Recur(x, y)

Termination == <>[]<>(pc = "done")

Correctness == \A s \in StateSpace : 
                    /\ pc[s] = "done"
                    => v[s] = GCD(u_ini[s], v_ini[s])

StateSpace == {s \in [pc: STRING, u_ini: 1..MaxNum, v_ini: 1..MaxNum, u: 1..MaxNum, v: 1..MaxNum] :
                  /\ s["pc"] \in {"start", "done"}
                  /\ s["u"] \leq s["u_ini"]
                  /\ s["v"] \leq s["v_ini"]}

====