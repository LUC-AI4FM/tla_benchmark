------------------------------ MODULE Euclid ------------------------------

EXTENDS Naturals, TLC

CONSTANT MaxNum

RECURSIVE GCD(_, _)
GCD(m, n) ==
  IF m = 0 THEN n ELSE GCD(n % m, m)

(*
--algorithm EuclidAlg
variables 
  u_ini \in 1..MaxNum,
  v_ini \in 1..MaxNum,
  u = u_ini,
  v = v_ini;

begin
  while u # v do
    if u > v then
      u := u - v;
    else
      v := v - u;
    end if;
  end while;
  assert u = v;
  assert u = GCD(u_ini, v_ini);
end algorithm
*)

VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "loop"

LoopStep ==
  /\ pc = "loop"
  /\ u # v
  /\ IF u > v
        THEN /\ u' = u - v
             /\ v' = v
        ELSE /\ u' = u
             /\ v' = v - u
  /\ pc' = "loop"
  /\ UNCHANGED << u_ini, v_ini >>

DoneStep ==
  /\ pc = "loop"
  /\ u = v
  /\ Assert(u = GCD(u_ini, v_ini), "Final correctness: u must equal GCD(u_ini, v_ini)")
  /\ PrintT("ReachedDone", TRUE)
  /\ pc' = "Done"
  /\ UNCHANGED << u_ini, v_ini, u, v >>

Next == LoopStep \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
 Safety invariants
*)
TypeOK ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum

Positive ==
  /\ u \in Nat \ {0}
  /\ v \in Nat \ {0}

GCDPreserved ==
  GCD(u, v) = GCD(u_ini, v_ini)

Inv == TypeOK /\ Positive /\ GCDPreserved

(*
 Liveness and correctness properties for TLC
*)
Termination == <> (pc = "Done")

CorrectAtDone ==
  [](pc = "Done" => /\ u = v /\ u = GCD(u_ini, v_ini))

=============================================================================