```tla
MODULE SmallTransitionSystem

EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES x

Init == x = 0

Next ==
  \/ /\ x < MaxValue
     /\ x' = x + 1
  \/ /\ x >= MaxValue
     /\ x' = x

Spec ==
  /\ Init
  /\ [][Next]_<<x>>

INVARIANT x \in Nat
INVARIANT x >= 0
INVARIANT x <= MaxValue
```