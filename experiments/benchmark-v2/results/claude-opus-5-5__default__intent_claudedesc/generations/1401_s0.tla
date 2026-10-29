---------------------------- MODULE InstanceFairness ----------------------------
EXTENDS Naturals

VARIABLE y

------------------------------ MODULE Inner ------------------------------------
EXTENDS Naturals

VARIABLE x

InnerInit == x = 0

InnerStep == /\ x < 3
             /\ x' = x + 1

InnerFairness == WF_x(InnerStep)

InnerSpec == InnerInit /\ [][InnerStep]_x /\ InnerFairness
================================================================================