---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

(***************************************************************************
--algorithm EuclidAlg
variables u = 24; v \in 1 .. 50;
begin
Lbl_1: while u # 0 do
         if u < v then
           u := v || v := u;
         end if;
Lbl_2:   u := u - v;
       end while;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. 50
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ v' = v

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ u \in 0 .. 50
          /\ v \in 1 .. 50
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

\* On termination u = 0 and v divides 24 (v holds the gcd).
PartialCorrectness == (pc = "Done") => (u = 0 /\ 24 % v = 0)

=============================================================================