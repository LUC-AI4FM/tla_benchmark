----------------------------- MODULE Euclid -----------------------------

EXTENDS Naturals, Integers, TLC

CONSTANT MaxNum

(*
--algorithm euclid
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;
begin
  Loop:
    while (v # 0) do
      u, v := v, u % v;
    end while;
  Done:
    assert u = GCD(u_ini, v_ini);
end algorithm;
*)

Divides(d, n) ==
  /\ d \in Nat \ {0}
  /\ n \in Nat
  /\ \E k \in Nat : n = d * k

Min(a, b) == IF a <= b THEN a ELSE b

GCD(a, b) ==
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE
    CHOOSE d \in 1..Min(a, b) :
      Divides(d, a) /\ Divides(d, b) /\
      \A e \in 1..Min(a, b) : (Divides(e, a) /\ Divides(e, b)) => e <= d

VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "Loop"

DoStep ==
  /\ pc = "Loop"
  /\ v # 0
  /\ u' = v
  /\ v' = u % v
  /\ UNCHANGED << u_ini, v_ini >>
  /\ pc' = "Loop"

Finish ==
  /\ pc = "Loop"
  /\ v = 0
  /\ UNCHANGED << u_ini, v_ini, u, v >>
  /\ TLC!Assert(u = GCD(u_ini, v_ini), "Final u must equal GCD(u_ini, v_ini)")
  /\ pc' = "Done"

Next == DoStep \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
 Safety invariants
*)
TypeInv ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum
  /\ pc \in {"Loop", "Done"}

GCDInvariant == GCD(u, v) = GCD(u_ini, v_ini)

(*
 Liveness property (termination under weak fairness of Next)
*)
Termination == <> (pc = "Done")

(*
 Correctness of the final result
*)
Correctness == (pc = "Done") => (u = GCD(u_ini, v_ini))

============================================================================