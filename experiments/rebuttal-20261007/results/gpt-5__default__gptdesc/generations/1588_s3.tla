----------------------------- MODULE EuclidSpec -----------------------------

EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N >= 1

(*
--algorithm Euclid
variables u = 24, v \in 1..N, v_ini = v;
begin
Start:
  while v # 0 do
IfSwap:
    if u > v then
      u, v := v, u;
    end if;
Subtract:
    v := v - u;
  end while;
Done:
  skip;
end algorithm
*)

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v

Next ==
  \/ /\ pc = "Start"
     /\ IF v # 0 THEN pc' = "IfSwap" ELSE pc' = "Done"
     /\ UNCHANGED << u, v, v_ini >>
  \/ /\ pc = "IfSwap"
     /\ IF u > v
           THEN /\ u' = v
                /\ v' = u
           ELSE /\ u' = u
                /\ v' = v
     /\ v_ini' = v_ini
     /\ pc' = "Subtract"
  \/ /\ pc = "Subtract"
     /\ v' = v - u
     /\ u' = u
     /\ v_ini' = v_ini
     /\ pc' = "Start"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Termination == <> (pc = "Done")

TypeInv ==
  /\ u \in Nat
  /\ v \in Nat
  /\ v_ini \in 1..N
  /\ pc \in {"Start", "IfSwap", "Subtract", "Done"}

Divides(d, x) == \E k \in Nat : x = d * k

Max(S) == CHOOSE m \in S : \A x \in S : x <= m

GCD(a, b) ==
  IF a + b = 0
    THEN 0
    ELSE Max({ d \in 1..(a + b) : Divides(d, a) /\ Divides(d, b) })

GCDInv == GCD(u, v) = GCD(24, v_ini)

DoneInv == (pc = "Done") => /\ v = 0 /\ u = GCD(24, v_ini)

=============================================================================