---------------------------- MODULE FairCounter ----------------------------
EXTENDS Integers, Naturals, TLC

(* --fair algorithm counter
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
\* Type and safety invariants

TypeOK == /\ x \in 0..10
          /\ pc \in {"Loop", "Done"}

DoneImpliesTen == (pc = "Done") => (x = 10)

-----------------------------------------------------------------------------
\* Auxiliary named-state predicates

AtFive == x = 5

FinishLoop == /\ pc = "Loop"
              /\ x = 10

-----------------------------------------------------------------------------
\* TLC-based check on the number of states reached along a behavior.
\* x takes values 0..10 at label Loop (11 states) followed by one Done
\* state, so any behavior has depth at most 12.

PossibleCounts == /\ TLCGet("level") \in 1..12
                  /\ (pc = "Done") => TLCGet("level") = 12

-----------------------------------------------------------------------------
\* Liveness properties

EventuallyAtFive == <>AtFive

EventuallyFinishLoop == <>FinishLoop

LoopLeadsToDone == (pc = "Loop") ~> (pc = "Done")

=============================================================================