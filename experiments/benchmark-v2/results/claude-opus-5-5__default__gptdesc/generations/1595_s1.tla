---------------------------- MODULE FairCounter ----------------------------
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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK == /\ x \in 0..10
          /\ pc \in {"Lbl_1", "Done"}

DoneImpliesTen == (pc = "Done") => (x = 10)

-----------------------------------------------------------------------------
\* Auxiliary predicates

\* State predicate: the counter has reached five
AtFive == x = 5

\* State predicate: the loop is about to exit
FinishLoop == /\ pc = "Lbl_1"
              /\ x = 10

\* Liveness properties built from the auxiliary predicates
EventuallyAtFive == <>AtFive

EventuallyFinishLoop == <>FinishLoop

\* TLC-based check on the number of distinct (named) states generated.
\* The reachable states are x = 0..10 with pc = "Lbl_1" plus the final
\* "Done" state, i.e. at most 12 distinct states.
PossibleCounts == TLCGet("distinct") \in 0..12

=============================================================================