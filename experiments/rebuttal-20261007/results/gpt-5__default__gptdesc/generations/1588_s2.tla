------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

(*
--algorithm Euclid
variables u, v, v_ini;
begin
  Init:
    u := 24;
    v \in 1..N;
    v_ini := v;
  Loop:
    while (u # v) do
      if (u > v) then
        u := u - v;
      else
        v := v - u;
      end if;
    end while;
  Done:
    skip;
end algorithm;
*)

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "Loop"

SubU ==
  /\ pc = "Loop"
  /\ u > v
  /\ u' = u - v
  /\ v' = v
  /\ v_ini' = v_ini
  /\ pc' = "Loop"

SubV ==
  /\ pc = "Loop"
  /\ v > u
  /\ v' = v - u
  /\ u' = u
  /\ v_ini' = v_ini
  /\ pc' = "Loop"

DoneStep ==
  /\ pc = "Loop"
  /\ u = v
  /\ u' = u
  /\ v' = v
  /\ v_ini' = v_ini
  /\ pc' = "Done"

Next == SubU \/ SubV \/ DoneStep

TypeInv ==
  /\ u \in Nat
  /\ v \in Nat
  /\ v_ini \in 1..N
  /\ pc \in {"Loop", "Done"}

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")
============================================================================