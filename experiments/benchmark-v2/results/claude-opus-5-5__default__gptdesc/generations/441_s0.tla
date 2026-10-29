---- MODULE ToggleXY ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in Nat
          /\ y \in Nat

Init == /\ x = 0
        /\ y = 0

Next == /\ x' = 1 - x
        /\ y' = y

EnabledNext == ENABLED Next

EnabledStutterNext == ENABLED <<Next>>_vars

SafetySpec == Init /\ [][Next]_vars

LiveSpec == SafetySpec /\ WF_vars(Next)

Spec == LiveSpec

XInRange == x \in {0, 1}

YConstant == y = 0

Toggles == []<>(x = 1) /\ []<>(x = 0)
====