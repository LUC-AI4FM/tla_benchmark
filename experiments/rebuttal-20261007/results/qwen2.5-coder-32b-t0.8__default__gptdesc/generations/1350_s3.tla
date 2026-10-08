---- MODULE SingleVariableSpec ----
EXTENDS Naturals

CONSTANTS InitVal, MaxVal

VARIABLES x

Init == x = InitVal

Next == \/ /\ x < MaxVal
               /\ x' = x + 1
          \/ /\ x = MaxVal
               /\ x' = x

Spec ==
  WF_next(<< >>) /\
  Init \ E [][Next]_<< >> /\
  <>[][x = MaxVal]_

THEOREM Spec => []<>(x = MaxVal)

====