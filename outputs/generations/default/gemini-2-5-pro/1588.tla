---------------------------- MODULE Euclid ----------------------------
EXTENDS Integers, TLC

CONSTANT N

VARIABLES u, v, v_ini, pc

vars == <<u, v, v_ini, pc>>

(*--fair algorithm Euclid
{
  variables u = 24, v \in 1..N, v_ini = v;
  {
  E:
    while (u /= v) {
      if (u > v) {
        u := u - v;
      } else {
        v := v - u;
      }
    };
  Done:
    skip;
  }
}
*)

TypeOK == /\ u \in Int
          /\ v \in Int
          /\ v_ini \in 1..N
          /\ pc \in {"E", "Done"}

Init ==
    /\ u = 24
    /\ v \in 1..N
    /\ v_ini = v
    /\ pc = "E"

E == /\ pc = "E"
     /\ IF u /= v
        THEN /\ IF u > v
                THEN /\ u' = u - v
                     /\ v' = v
                ELSE /\ v' = v - u
                     /\ u' = u
             /\ pc' = "E"
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<u, v>>
     /\ UNCHANGED <<v_ini>>

Done == /\ pc = "Done"
        /\ UNCHANGED vars

Next == E \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================