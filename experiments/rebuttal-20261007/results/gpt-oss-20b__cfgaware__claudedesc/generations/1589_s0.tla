------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

VARIABLES pc, u, v, u_ini, v_ini

(* Helper function: GCD *)
GCD(x,y) ==
  MAX({d \in 1..x : (d \in 1..y) /\ (x % d = 0) /\ (y % d = 0)})

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "a"

A1 ==
  /\ pc = "a"
  /\ u # 0
  /\ ((u < v) /\ (u' = v /\ v' = u)) \/ ((u >= v) /\ (u' = u /\ v' = v))
  /\ pc' = "b"

A2 ==
  /\ pc = "a"
  /\ u = 0
  /\ v = GCD(u_ini, v_ini)
  /\ u' = u
  /\ v' = v
  /\ pc' = "Done"

B ==
  /\ pc = "b"
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "a"

Next == A1 \/ A2 \/ B

vars == <<pc, u, v, u_ini, v_ini>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

Invariant == [] ((pc = "Done") => (v = GCD(u_ini, v_ini)))

Finished == (pc = "Done")
SwapOccurs == (pc = "a" /\ u < v)

PossibleCounts ==
  Coverage(Finished) = 800
  /\ Coverage(SwapOccurs) = 698

=============================================================================