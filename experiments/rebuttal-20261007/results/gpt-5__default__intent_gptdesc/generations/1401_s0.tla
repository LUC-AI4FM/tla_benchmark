----------------------------- MODULE CounterSystem -----------------------------
EXTENDS Naturals

VARIABLES obs

vars == << obs >>

Init ==
  obs = 0

CanInc ==
  obs < 3

SubInc ==
  /\ CanInc
  /\ obs' = obs + 1

ControllerStutter ==
  /\ ~CanInc
  /\ UNCHANGED obs

Next ==
  SubInc \/ ControllerStutter

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SubInc)

(*
 Safety properties
*)
TypeInv ==
  obs \in 0..3

StepChangeConstraint ==
  (obs' = obs) \/ (obs' = obs + 1 /\ obs < 3)

Safety_OnlyIncOrStutter ==
  [] StepChangeConstraint

NoChangeWhenDisabled ==
  [] (~CanInc => obs' = obs)

(*
 Liveness goal
*)
LivenessGoal ==
  <> (obs = 3)

(*
 Proof obligations / properties to be checked
*)
THEOREM TypeInvariant == Spec => []TypeInv

THEOREM ChangeSafety == Spec => Safety_OnlyIncOrStutter

THEOREM StutterWhenDisabled == Spec => NoChangeWhenDisabled

THEOREM LivenessHolds == Spec => LivenessGoal
=============================================================================