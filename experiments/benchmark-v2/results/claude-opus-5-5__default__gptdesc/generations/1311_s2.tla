---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

(***************************************************************************
--algorithm Euclid
variables u = 24 ; v \in 1 .. 50 ;
begin
Lbl_1: while u # 0 do
         if u < v then
           u := v || v := u ;
         end if ;
Lbl_2:   u := u - v ;
       end while ;
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
                          THEN /\ u' = v
                               /\ v' = u
                          ELSE /\ UNCHANGED << u, v >>
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

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ u \in Nat
          /\ v \in 1 .. 50
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

\* Before each subtraction, u is at least v, so u never goes negative.
SubtractionSafe == (pc = "Lbl_2") => (u >= v)

\* On termination u has reached 0, and v holds the result.
DoneCorrect == (pc = "Done") => (u = 0 /\ v \in 1 .. 50)

=============================================================================