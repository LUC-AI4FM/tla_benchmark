---- MODULE TheoremRefs ----
EXTENDS Naturals

---- MODULE Inner ----
CONSTANT D
VARIABLE y

IInit   == y = 0
INext   == y' = IF y < D THEN y + 1 ELSE 0
ISpec   == IInit /\ [][INext]_y
ITypeOK == y \in 0..D

ASSUME InnerAssume == D \in Nat

THEOREM InnerThm == ISpec => []ITypeOK
====