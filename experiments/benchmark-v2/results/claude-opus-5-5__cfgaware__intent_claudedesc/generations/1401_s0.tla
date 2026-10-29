---------------------------- MODULE InstanceFairness ----------------------------
EXTENDS Naturals

---------------------------- MODULE InnerCounter ----------------------------
EXTENDS Naturals

VARIABLE x

InnerInit == x = 0

InnerStep == x < 3 /\ x' = x + 1

InnerFair == WF_x(InnerStep)

InnerSpec == InnerInit /\ [][InnerStep]_x /\ InnerFair
=============================================================================