---------------------------- MODULE FairCounter ----------------------------
EXTENDS Naturals, TLC

(* --fair algorithm FairCounter
variable x = 0;
begin
  Loop:
    while x < 10 do
      x := x + 1;
    end while;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == /\ x = 0
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF x < 10
              THEN /\ x' = x + 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ x \in 0..10
          /\ pc \in {"Loop", "Done"}

DoneImpliesTen == (pc = "Done") => (x = 10)

-----------------------------------------------------------------------------
(* Auxiliary predicates *)

AtFive == x = 5

FinishLoop == /\ pc = "Loop"
              /\ x = 10

(* TLC-based check about named-state counts: the counter yields exactly
   eleven distinct "Loop" states (x = 0..10) plus one "Done" state, so the
   number of distinct states TLC ever discovers is bounded by 12, and the
   behavior depth never exceeds 12. *)
PossibleCounts == /\ TLCGet("distinct") <= 12
                  /\ TLCGet("level") <= 12

-----------------------------------------------------------------------------
(* Liveness properties *)

EventuallyAtFive == <>AtFive

EventuallyFinishLoop == <>FinishLoop

FinishLoopLeadsToDone == FinishLoop ~> (pc = "Done")

=============================================================================