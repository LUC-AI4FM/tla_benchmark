---------------------------- MODULE InstanceWithComma ----------------------------
EXTENDS Naturals, TLC

---------------------------- MODULE InnerMod ----------------------------
EXTENDS Naturals
CONSTANTS A, B
Sum == A + B
==========================================================================