------------------------------ MODULE DieHard ------------------------------
EXTENDS Naturals, TLC

CONSTANT smallCap \in Nat
CONSTANT bigCap \in Nat

VARIABLES small, big, usage

(* Type invariant for water amounts *)
TypeInv ==
  /\ small >= 0 /\ small <= smallCap
  /\ big   >= 0 /\ big   <= bigCap
  /\ usage >= 0

Init == 
  /\ small = 0
  /\ big   = 0
  /\ usage = 0
  /\ TypeInv

FillSmall ==
  /\ small' = smallCap
  /\ big'   = big
  /\ usage' = usage + (smallCap - small)

EmptySmall ==
  /\ small' = 0
  /\ big'   = big
  /\ usage' = usage

PourSmallToBig ==
  LET transfer == IF small <= bigCap - big THEN small ELSE bigCap - big IN
  /\ small' = small - transfer
  /\ big'   = big + transfer
  /\ usage' = usage

FillBig ==
  /\ big'   = bigCap
  /\ small' = small
  /\ usage' = usage + (bigCap - big)

EmptyBig ==
  /\ big'   = 0
  /\ small' = small
  /\ usage' = usage

PourBigToSmall ==
  LET transfer == IF big <= smallCap - small THEN big ELSE smallCap - small IN
  /\ big'   = big - transfer
  /\ small' = small + transfer
  /\ usage' = usage

Stutter ==
  /\ small' = small
  /\ big'   = big
  /\ usage' = usage

Next == 
  \/ FillSmall
  \/ EmptySmall
  \/ PourSmallToBig
  \/ FillBig
  \/ EmptyBig
  \/ PourBigToSmall
  \/ Stutter

vars == <<small, big, usage>>

Spec == Init /\ [][Next]_vars

(* Safety invariant *)
Inv == TypeInv

THEOREM InvIsInvariant == Spec => []Inv

(* Liveness property: eventually the big jug has 4 gallons *)
LivenessProp == <> (big = 4)
THEOREM EventuallyBigFour == Spec => <> (big = 4)

END ------------------------------ MODULE DieHard ------------------------------