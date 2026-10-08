MODULE SimpleState
EXTENDS Naturals

CONSTANTS AllowedSet, Threshold, BoolCond

VARIABLE x

NumPred(v) == v > Threshold
BoolReq(v) == BoolCond[v]

Init ==
  /\ x \in AllowedSet
  /\ NumPred(x)
  /\ BoolReq(x)

Next ==
  /\ x' = x

Spec ==
  Init /\ [][Next]_x

SafetyInvariant ==
  /\ x \in AllowedSet
  /\ NumPred(x)
  /\ BoolReq(x)

THEOREM SpecImplySafety == Spec => []SafetyInvariant

THEOREM ValidInitExists == 
  EXISTS v \in AllowedSet : NumPred(v) /\ BoolReq(v)