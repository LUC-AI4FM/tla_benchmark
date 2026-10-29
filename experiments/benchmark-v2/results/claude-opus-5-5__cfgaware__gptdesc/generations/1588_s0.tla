------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC

CONSTANT N

(***************************************************************************
--algorithm Euclid {
  variables u = 24 ; v \in 1..N ; v_ini = v ;
  {  while (u # 0) {
       if (u < v) { u := v || v := u } ;
       u := u - v
     } ;
     print <<24, v_ini, "have gcd", v>>
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<24, v_ini, "have gcd", v>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ UNCHANGED v_ini

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << v, v_ini >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================