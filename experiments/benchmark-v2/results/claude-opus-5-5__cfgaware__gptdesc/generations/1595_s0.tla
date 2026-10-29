---- MODULE FairCounter ----
EXTENDS Naturals, TLC

(* --fair algorithm FairCounter
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

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ x \in 0..10
          /\ pc \in {"Lbl_1", "Done"}

AtFive == x = 5

FinishLoop == pc = "Lbl_1" /\ x = 10

_POSSIBLE == <>AtFive /\ <>FinishLoop

PossibleCounts == TLCGet("stats").distinct <= 12

====