---------------------------- MODULE FairCounter ----------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x = 0
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ x < 10
    /\ x' = x + 1
    /\ pc' = "loop"

ExitLoop ==
    /\ pc = "loop"
    /\ x >= 10
    /\ pc' = "Done"
    /\ x' = x

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ ExitLoop
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Invariants *)

TypeInvariant ==
    /\ x \in 0..10
    /\ pc \in {"loop", "Done"}

XBounded ==
    x >= 0 /\ x <= 10

SafetyInvariant ==
    /\ TypeInvariant
    /\ XBounded

-----------------------------------------------------------------------------
(* Auxiliary Predicates *)

AtFive ==
    x = 5

FinishLoop ==
    pc = "Done"

PossibleCounts ==
    x \in 0..10

-----------------------------------------------------------------------------
(* Liveness Properties *)

Termination ==
    <>(pc = "Done")

EventuallyTen ==
    <>(x = 10)

=============================================================================