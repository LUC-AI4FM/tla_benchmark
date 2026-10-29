---------------------------- MODULE TopLevelCommaInstance ----------------------------
EXTENDS Naturals, TLC

---------------------------- MODULE SumModule ----------------------------
EXTENDS Naturals
CONSTANTS A, B

Sum == A + B
==========================================================================