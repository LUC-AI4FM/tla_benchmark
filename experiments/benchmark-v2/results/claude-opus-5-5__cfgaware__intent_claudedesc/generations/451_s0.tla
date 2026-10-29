---------------------------- MODULE InstanceTest ----------------------------
EXTENDS Naturals

------------------------------ MODULE Inner ------------------------------
VARIABLE x

InnerInit == x = 0

InnerNext == x' = (x + 1) % 5

InnerSpec == InnerInit /\ [][InnerNext]_x

InnerTypeOK == x \in 0..4
==========================================================================