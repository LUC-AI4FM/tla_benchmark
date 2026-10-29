---------------------------- MODULE ParamInstance ----------------------------
EXTENDS Naturals

---------------------------- MODULE Inner ----------------------------
VARIABLE y

InnerInit == y = 0

InnerNext == y' = (y + 1) % 5

InnerSpec == InnerInit /\ [][InnerNext]_y
========================================================================