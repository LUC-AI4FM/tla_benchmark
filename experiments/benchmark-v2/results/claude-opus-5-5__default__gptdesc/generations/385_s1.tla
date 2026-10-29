---------------------------- MODULE TheoremRefs ----------------------------
EXTENDS Naturals

CONSTANT C

VARIABLE x

----------------------------- MODULE Inner -----------------------------
EXTENDS Naturals

CONSTANT D

VARIABLE y

ASSUME InnerAssump == D \in Nat

InnerTypeOK == y \in Nat

InnerInit == y = 0

InnerNext == y' = y + D

InnerSpec == InnerInit /\ [][InnerNext]_y

InnerLive == WF_y(InnerNext)

THEOREM InnerThm == InnerSpec => []InnerTypeOK
=========================================================================