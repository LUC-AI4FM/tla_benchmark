---------------------------- MODULE SimpleSystem ----------------------------
EXTENDS Integers

CONSTANT InitialValue, AllowedValues

VARIABLE state

Init == state = InitialValue

NextState(ok) == 
  IF ok THEN 
    state' = (CHOOSE v \in AllowedValues : v > 0)
  ELSE 
    state' = state

Next == (\E ok \in {TRUE, FALSE} : NextState(ok))

Spec == Init /\ [][Next]_state

TypeInvariant == state \in Int

SafetyInvariant == state # 0

TransitionConstraint == 
  \A s \in [Spec]_state : 
    (s # 0) /\ (\A t \in [Spec]_state : 
      (t = s) \/ (\E v \in AllowedValues : (v > 0) /\ (t = v)))

THEOREM Spec => []SafetyInvariant
THEOREM Spec => TransitionConstraint

=============================================================================