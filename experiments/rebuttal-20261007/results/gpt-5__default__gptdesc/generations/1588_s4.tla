------------------------------ MODULE EuclidAlgorithm ------------------------------

EXTENDS Naturals

CONSTANT N

(*
--algorithm Euclid
variables u = 24, v \in 1..N, v_ini = v;
begin A:
  while (u /= v) do
    if (u < v) then
      u, v := v, u;
    else
      u := u - v;
    end if;
  end while;
Done:
  skip;
end algorithm;
*)

VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "A"

A_Swap ==
  /\ pc = "A"
  /\ u /= v
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ v_ini' = v_ini
  /\ pc' = "A"

A_Sub ==
  /\ pc = "A"
  /\ u /= v
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ v_ini' = v_ini
  /\ pc' = "A"

A_Done ==
  /\ pc = "A"
  /\ u = v
  /\ UNCHANGED << u, v, v_ini >>
  /\ pc' = "Done"

Done_Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ A_Swap
  \/ A_Sub
  \/ A_Done
  \/ Done_Stutter

TypeInv ==
  /\ u \in Nat \ {0}
  /\ v \in Nat \ {0}
  /\ v_ini \in 1..N
  /\ pc \in {"A", "Done"}

Termination ==
  <> (pc = "Done")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

=============================================================================