--------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, Sequences, TemporalOperators

CONSTANT MaxNum \* Upper bound on the input numbers (MaxNum > 0)

VARIABLES pc, u_ini, v_ini, u, v, cnt
vars == <<pc, u_ini, v_ini, u, v, cnt>>

EuclidGcd(x, y) ==
  IF y = 0 THEN x ELSE EuclidGcd(y, Mod(x, y))

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ cnt = 0
  /\ pc = "START"

Start ==
  /\ pc = "START"
  /\ pc' = "LOOP"
  /\ UNCHANGED <<u, v, cnt, u_ini, v_ini>>

Loop1 ==
  /\ pc = "LOOP"
  /\ u > v
  /\ u' = u - v
  /\ v' = v
  /\ cnt' = cnt + 1
  /\ pc' = pc
  /\ UNCHANGED <<u_ini, v_ini>>

Loop2 ==
  /\ pc = "LOOP"
  /\ u <= v
  /\ u' = u
  /\ v' = v - u
  /\ cnt' = cnt + 1
  /\ pc' = pc
  /\ UNCHANGED <<u_ini, v_ini>>

Done ==
  /\ pc = "LOOP"
  /\ u = v
  /\ pc' = "DONE"
  /\ UNCHANGED <<pc, u_ini, v_ini, u, v, cnt>>

Next == Start \/ Loop1 \/ Loop2 \/ Done

Spec == Init /\ [][Next]_vars

GcdCorrectness ==
  (pc = "DONE") => (u = EuclidGcd(u_ini, v_ini))

Safety ==
  GcdCorrectness /\ cnt >= 0

Liveness ==
  WF_vars(Next)

=============================================================================