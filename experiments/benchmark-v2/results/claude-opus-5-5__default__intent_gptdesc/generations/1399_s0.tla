---------------------------- MODULE BooleanToggle ----------------------------
EXTENDS Naturals

VARIABLES state

vars == << state >>

-----------------------------------------------------------------------------
(* Initial condition: the state starts as TRUE *)
Init == state = TRUE

(* Flip the state to its logical negation *)
Flip == state' = ~state

(* Stuttering step: leave the state unchanged *)
Stutter == UNCHANGED state

(* Transition relation: either flip or stutter *)
Next == Flip \/ Stutter

(* Full temporal behavior: initial condition conjoined with box-of-steps *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety: the state is always a boolean; no illegal values appear *)
TypeOK == state \in BOOLEAN

NoIllegalValues == state = TRUE \/ state = FALSE

(* Strong invariant claim: the state is always TRUE.
   This does NOT hold, since Flip may set state to FALSE. *)
StrongInv == state = TRUE

(* Weaker observational claim: the state is either TRUE or its negation
   holds; this holds throughout every execution. *)
WeakInv == state \/ ~state

-----------------------------------------------------------------------------
(* Liveness / enabledness: the system is never deadlocked *)
NotDeadlocked == ENABLED Next

(* Transitions are always enabled: either the state can flip or stuttering
   is allowed *)
AlwaysEnabled == ENABLED Flip \/ ENABLED Stutter

DeadlockFreedom == [](ENABLED Next)

TransitionsEnabled == [](ENABLED Flip \/ ENABLED Stutter)

-----------------------------------------------------------------------------
(* Theorems / proof obligations *)
THEOREM TypeCorrect == Spec => []TypeOK
THEOREM NoIllegal == Spec => []NoIllegalValues
THEOREM WeakHolds == Spec => []WeakInv
THEOREM NoDeadlock == Spec => DeadlockFreedom
THEOREM Enabledness == Spec => TransitionsEnabled
(* Note: Spec => []StrongInv is NOT a theorem; it is expected to be
   violated by model checking, for comparison with WeakInv. *)

=============================================================================