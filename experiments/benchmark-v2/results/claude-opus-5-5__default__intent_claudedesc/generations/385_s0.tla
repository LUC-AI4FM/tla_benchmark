---------------------------- MODULE TheoremInstanceTest ----------------------------
EXTENDS Naturals

  ------------------------------- MODULE Inner -------------------------------
  CONSTANT C

  Def == C + 1

  InnerProp == /\ C = 2
               /\ Def = 3

  InnerLabeled == lab :: (C + C = 4)

  InnerNat == C \in Nat

  THEOREM InnerThm == InnerProp
  THEOREM InnerThm2 == InnerNat
  =============================================================================