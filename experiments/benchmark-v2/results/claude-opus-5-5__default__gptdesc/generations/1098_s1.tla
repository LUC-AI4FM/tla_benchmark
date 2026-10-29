---------------------------- MODULE MCLamportMutex ----------------------------
EXTENDS LamportMutex

CONSTANT MaxNat

ASSUME MaxNatAssumption == MaxNat \in Nat

NatOverride == 0 .. MaxNat

===============================================================================