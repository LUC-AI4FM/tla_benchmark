---------------------------- MODULE ParamInstance ----------------------------
EXTENDS Naturals

CONSTANT D

ASSUME DAssumption == D = 4

---------------------------- MODULE Sub ----------------------------
EXTENDS Naturals

CONSTANTS P, K, Tag

ASSUME SubAssumption == P \in Nat /\ K \in Nat

SubVal == P + K
SubOK  == P = 4 /\ K = 2
=====================================================================