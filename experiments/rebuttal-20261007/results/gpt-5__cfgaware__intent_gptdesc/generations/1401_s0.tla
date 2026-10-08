------------------------------ MODULE TwoComponentCounter ------------------------------

EXTENDS Naturals

(*
  Two-component concurrent system:
  - Subcomponent: bounded counter that increments from 0 up to 3, one per step.
  - Main controller: exposes the subcomponent's local counter as the shared observable value.
  - Global behavior: persistent step relation with stuttering semantics.
  - Fairness: weak fairness on the subcomponent's increment action.
*)

VARIABLES obs

vars == << obs >>

Max == 3

Init ==
  /\ obs = 0

(*
  Subcomponent's increment action: enabled exactly when obs < Max,
  and increments obs by 1.
*)
Inc ==
  /\ obs < Max
  /\ obs' = obs + 1

(*
  Main controller stutter action: permitted when the subcomponent
  increment is not enabled; leaves the observable value unchanged.
*)
Stutter ==
  /\ ~Enabled(Inc)
  /\ UNCHANGED obs

(*
  Global next-step relation: either the subcomponent increments,
  or (when not enabled) the controller stutters.
*)
Next ==
  Inc \/ Stutter

(*
  Safety requirements:
  - Only state changes are increments by 1 while enabled.
  - Stutter steps do not change the observable value.
  - The observable value always stays within bounds 0..Max.
*)
TypeInv ==
  [] (obs \in 0..Max)

StepSafety ==
  [] ( (/\ obs < Max /\ obs' = obs + 1) \/ UNCHANGED obs )

(*
  Fairness: weak fairness ensures that if Inc remains continuously
  enabled, it cannot be postponed indefinitely.
*)
Fairness ==
  WF_vars(Inc)

(*
  System specification with persistent step relation and stuttering semantics.
*)
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

(*
  Liveness goal: eventually the observable value reaches Max (= 3).
*)
Prop ==
  <> (obs = Max)

=============================================================================