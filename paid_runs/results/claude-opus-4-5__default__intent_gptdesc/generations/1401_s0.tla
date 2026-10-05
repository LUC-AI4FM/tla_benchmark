-------------------------------- MODULE TwoComponentSystem --------------------------------

EXTENDS Integers

CONSTANTS MaxCount

ASSUME MaxCount = 3

VARIABLES observable

vars == <<observable>>

-----------------------------------------------------------------------------
(* Subcomponent: performs bounded counting from 0 to MaxCount *)

SubcomponentEnabled == observable < MaxCount

SubcomponentIncrement == 
    /\ SubcomponentEnabled
    /\ observable' = observable + 1

-----------------------------------------------------------------------------
(* Main Controller: can only stutter when subcomponent is not enabled *)

ControllerStutter ==
    /\ ~SubcomponentEnabled
    /\ observable' = observable

-----------------------------------------------------------------------------
(* Initial state *)

Init == observable = 0

-----------------------------------------------------------------------------
(* Next state relation: either subcomponent increments or controller stutters *)

Next == 
    \/ SubcomponentIncrement
    \/ ControllerStutter

-----------------------------------------------------------------------------
(* Specification with weak fairness on subcomponent increment *)

Fairness == WF_vars(SubcomponentIncrement)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Type invariant: observable is always in valid range
TypeInvariant == observable \in 0..MaxCount

\* Safety: observable value is bounded
SafetyBounded == observable >= 0 /\ observable <= MaxCount

\* Safety property: state changes only increment by 1 or stutter
\* Expressed as a temporal property on transitions
SafetyIncrementOrStutter == 
    [][observable' = observable + 1 \/ observable' = observable]_vars

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Eventually the observable value reaches MaxCount (3)
EventuallyReachesMax == <>(observable = MaxCount)

\* The subcomponent eventually completes its task
LivenessGoal == EventuallyReachesMax

-----------------------------------------------------------------------------
(* Proof Obligations / Properties to Check *)

\* Main theorem: Under the specification (including fairness), 
\* the observable value eventually reaches 3
THEOREM Spec => EventuallyReachesMax

\* Safety theorem: The type invariant is always maintained
THEOREM Spec => []TypeInvariant

\* Safety theorem: Only valid transitions occur
THEOREM Spec => SafetyIncrementOrStutter

=============================================================================