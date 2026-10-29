---------------------------- MODULE EnabledInstance ----------------------------
EXTENDS Naturals

VARIABLE x

---------------------------- MODULE Inner ----------------------------
EXTENDS Naturals

VARIABLE s

Step == s' = (s + 1) % 3

EnStep == ENABLED Step

P == ENABLED (s' = s + 1 /\ s' < 3)

Q == ENABLED (s' = s /\ s < 3)
======================================================================