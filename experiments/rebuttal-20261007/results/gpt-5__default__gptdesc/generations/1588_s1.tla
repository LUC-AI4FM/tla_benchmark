----------------------------- MODULE Euclid -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

(*
--algorithm EuclidAlg
variables u = 24, v \in 1..N, v_ini = v;
begin
A:
  while v # 0 do
B:
    while u >= v do
      u := u - v;
    end while;
C:
    u, v := v, u; \* swap
  end while;
Done:
  skip;
end algorithm
*)

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

Max(S) == CHOOSE m \in S : \A n \in S : n <= m

Divides(d, m) == \E k \in Nat : m = k * d

GCD(m, n) ==
  IF m = 0 /\ n = 0 THEN 0
  ELSE
    LET S == { d \in 1..(m + n) : Divides(d, m) /\ Divides(d, n) } IN
      IF S = {} THEN 0 ELSE Max(S)

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "A"

A_Step ==
  /\ pc = "A"
  /\ IF v # 0 THEN pc' = "B" ELSE pc' = "Done"
  /\ UNCHANGED << u, v, v_ini >>

B_Step ==
  /\ pc = "B"
  /\ IF u >= v THEN pc' = "Sub" ELSE pc' = "Swap"
  /\ UNCHANGED << u, v, v_ini >>

Sub_Step ==
  /\ pc = "Sub"
  /\ u' = u - v
  /\ pc' = "B"
  /\ UNCHANGED << v, v_ini >>

Swap_Step ==
  /\ pc = "Swap"
  /\ /\ u' = v
     /\ v' = u
  /\ pc' = "A"
  /\ UNCHANGED v_ini

Next ==
  \/ A_Step
  \/ B_Step
  \/ Sub_Step
  \/ Swap_Step

TypeInv ==
  /\ u \in Nat
  /\ v \in Nat
  /\ v_ini \in 1..N

GcdInv ==
  GCD(u, v) = GCD(24, v_ini)

Termination ==
  <> (pc = "Done")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

============================================================================