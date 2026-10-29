---------------------------- MODULE Counter ----------------------------
EXTENDS Naturals, TLC

(* --algorithm Counter
variables x = 0;
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

TypeOK == /\ x \in 0..10
          /\ pc \in {"Lbl_1", "Done"}

(* Holds when the counter is at five. *)
AtFive == x = 5

(* Holds when x = 9 and x is about to become 10. *)
FinishLoop == x = 9 /\ x' = 10

(* Properties tracked as _POSSIBLE for model checking. *)
AtFive_POSSIBLE == AtFive
FinishLoop_POSSIBLE == FinishLoop

(* Postcondition: each _POSSIBLE property is witnessed exactly once. *)
PossibleCounts ==
    LET possible == TLCGet("spec").possible
    IN  /\ \E i \in DOMAIN possible :
              /\ possible[i].name = "AtFive"
              /\ possible[i].count = 1
        /\ \E i \in DOMAIN possible :
              /\ possible[i].name = "FinishLoop"
              /\ possible[i].count = 1

=============================================================================