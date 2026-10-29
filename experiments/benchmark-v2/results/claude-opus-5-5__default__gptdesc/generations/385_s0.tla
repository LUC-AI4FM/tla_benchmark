---------------------------- MODULE TheoremRefs ----------------------------
EXTENDS Naturals

CONSTANT C
VARIABLE x

ASSUME ConstAssump == C \in Nat \ {0}

------------------------------ MODULE Inner ------------------------------
CONSTANT D
VARIABLE y

ASSUME InnerAssump == D \in Nat

IInit == y = 0

INext == \/ /\ y < D
            /\ y' = y + 1
         \/ /\ y = D
            /\ y' = 0

ISpec == IInit /\ [][INext]_y /\ WF_y(INext)

ITypeOK == y \in 0..D

ILive == []<>(y = 0)

THEOREM InnerThm == ISpec => []ITypeOK
PROOF OMITTED

THEOREM InnerLiveThm == ISpec => ILive
PROOF OMITTED
==========================================================================