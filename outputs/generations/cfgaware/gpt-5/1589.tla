------------------------------- MODULE Euclid -------------------------------

EXTENDS Naturals

CONSTANT MaxNum
ASSUME MaxNum \in Nat /\ MaxNum > 0

(*
--algorithm euclid
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;

begin
Loop:
  while (v # 0) do
    with t = u % v do
      u := v;
      v := t;
    end with;
  end while;
Done:
  skip;
end algorithm;
*)

(*
--algorithm euclid translation
*)

VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

RECURSIVE GCD(_,_)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "Loop"

LoopStep ==
  /\ pc = "Loop"
  /\ v # 0
  /\ u' = v
  /\ v' = u % v
  /\ pc' = "Loop"
  /\ UNCHANGED << u_ini, v_ini >>

DoneStep ==
  /\ pc = "Loop"
  /\ v = 0
  /\ pc' = "Done"
  /\ UNCHANGED << u, v, u_ini, v_ini >>

Next == LoopStep \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Invariant ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 0..MaxNum
  /\ v \in 0..MaxNum
  /\ pc \in {"Loop", "Done"}
  /\ GCD(u, v) = GCD(u_ini, v_ini)
  /\ (pc = "Done" => /\ v = 0
                     /\ u = GCD(u_ini, v_ini))

Termination == <> (pc = "Done")

=============================================================================