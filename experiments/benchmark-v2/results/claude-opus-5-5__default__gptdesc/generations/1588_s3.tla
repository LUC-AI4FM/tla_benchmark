---- MODULE Euclid ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

(***************************************************************************
--algorithm Euclid {
  variables u = 24, v \in 1..N, v_ini = v;
  {
    a: while (u # 0) {
         if (u < v) { u := v || v := u };
         b: u := u - v
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ /\ u' = v
                              /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ v_ini' = v_ini

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << v, v_ini >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ u \in Nat
          /\ v \in Nat
          /\ v_ini \in 1..N
          /\ pc \in {"a", "b", "Done"}

====