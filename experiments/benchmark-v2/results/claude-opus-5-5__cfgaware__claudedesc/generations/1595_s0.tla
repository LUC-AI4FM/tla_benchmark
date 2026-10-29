------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals, TLC

(* --algorithm Counter
variable x = 0;
begin
Lbl_1:
  while x < 10 do
    x := x + 1;
  end while;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == /\ x = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x < 10
               THEN /\ x' = x + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------

AtFive == x = 5

FinishLoop == x = 9 /\ pc = "Lbl_1"

(* Initialize the witness counters (register 1: AtFive, register 2: FinishLoop). *)
ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

(* Checked on every distinct reachable state; records each time a          *)
(* tracked predicate is witnessed. Always evaluates to TRUE.              *)
_POSSIBLE ==
    /\ IF AtFive     THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF FinishLoop THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

(* Postcondition: each tracked predicate was witnessed exactly once. *)
PossibleCounts ==
    /\ TLCGet(1) = 1
    /\ TLCGet(2) = 1

=============================================================================