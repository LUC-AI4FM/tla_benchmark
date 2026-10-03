---- MODULE Euclid ----
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES u, v, v_ini, pc

(*
--algorithm EuclidAlg
variables u = 24, v \in 1..N, v_ini = v;

begin
Start:
  if v = 0 then
    goto Done;
  else
    goto Step;
  end if;

Step:
  if u < v then
    u, v := v, u;
  else
    u := u - v;
  end if;
  goto Start;

Done:
  skip;
end algorithm
*)

vars == << u, v, v_ini, pc >>

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "Start"

Next ==
  \/ /\ pc = "Start"
     /\ v = 0
     /\ pc' = "Done"
     /\ UNCHANGED << u, v, v_ini >>
  \/ /\ pc = "Start"
     /\ v # 0
     /\ pc' = "Step"
     /\ UNCHANGED << u, v, v_ini >>
  \/ /\ pc = "Step"
     /\ u < v
     /\ u' = v
     /\ v' = u
     /\ pc' = "Start"
     /\ UNCHANGED v_ini
  \/ /\ pc = "Step"
     /\ u >= v
     /\ u' = u - v
     /\ v' = v
     /\ pc' = "Start"
     /\ UNCHANGED v_ini

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination ==
  <> (pc = "Done")

====