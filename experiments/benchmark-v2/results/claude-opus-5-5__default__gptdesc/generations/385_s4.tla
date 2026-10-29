---------------------------- MODULE TheoremRefs ----------------------------
EXTENDS Naturals

CONSTANT C
VARIABLE x

---------------------------- MODULE Inner ----------------------------------
EXTENDS Naturals

CONSTANT D
VARIABLE y

ASSUME InnerAssume == D \in Nat

IInit == y = 0

INext == y' = IF y < D THEN y + 1 ELSE 0

ISpec == IInit /\ [][INext]_y

ITypeOK == y \in 0..D

THEOREM InnerThm == ISpec => []ITypeOK
=============================================================================