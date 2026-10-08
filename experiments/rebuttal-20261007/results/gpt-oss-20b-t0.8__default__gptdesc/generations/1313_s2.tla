MODULE DieHard
EXTENDS Naturals

CONSTANT SmallCap = 3, BigCap = 5

VARIABLES small, big, usedWater

Init ==
  /\ small = 0
  /\ big   = 0
  /\ usedWater = 0

FillSmall ==
  /\ small' = SmallCap
  /\ big'   = big
  /\ usedWater' = usedWater + SmallCap

EmptySmall ==
  /\ small' = 0
  /\ big'   = big
  /\ usedWater' = usedWater

FillBig ==
  /\ big'   = BigCap
  /\ small' = small
  /\ usedWater' = usedWater + BigCap

EmptyBig ==
  /\ big'   = 0
  /\ small' = small
  /\ usedWater' = usedWater

PourSmallToBig ==
  LET transfer == Min(small, BigCap - big) IN
  /\ small' = small - transfer
  /\ big'   = big + transfer
  /\ usedWater' = usedWater

PourBigToSmall ==
  LET transfer == Min(big, SmallCap - small) IN
  /\ big'   = big - transfer
  /\ small' = small + transfer
  /\ usedWater' = usedWater

Stutter ==
  /\ small'    = small
  /\ big'      = big
  /\ usedWater'= usedWater

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ FillBig
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall
  \/ Stutter

vars == <<small, big, usedWater>>

(* Safety invariants *)
WaterAmountsInRange ==
  /\ small >= 0   /\ small <= SmallCap
  /\ big   >= 0   /\ big   <= BigCap

UsedWaterMonotonic ==
  /\ usedWater' >= usedWater

Safety == WaterAmountsInRange

(* Liveness property: eventually the big jug contains exactly 4 gallons *)
EventuallyBig4 == <> (big = 4)

Liveness == EventuallyBig4

Spec == Init /\ [][Next]_vars

\* The full specification including safety and liveness
FullSpec == Spec /\ Safety

=============================================================================

MODULE DieHard
CONSTANTS SmallCap, BigCap
VARIABLES small, big, usedWater

Init ==
  /\ small = 0
  /\ big   = 0
  /\ usedWater = 0

FillSmall ==
  /\ small' = SmallCap
  /\ big'   = big
  /\ usedWater' = usedWater + SmallCap

EmptySmall ==
  /\ small' = 0
  /\ big'   = big
  /\ usedWater' = usedWater

FillBig ==
  /\ big'   = BigCap
  /\ small' = small
  /\ usedWater' = usedWater + BigCap

EmptyBig ==
  /\ big'   = 0
  /\ small' = small
  /\ usedWater' = usedWater

PourSmallToBig ==
  LET transfer == Min(small, BigCap - big) IN
  /\ small' = small - transfer
  /\ big'   = big + transfer
  /\ usedWater' = usedWater

PourBigToSmall ==
  LET transfer == Min(big, SmallCap - small) IN
  /\ big'   = big - transfer
  /\ small' = small + transfer
  /\ usedWater' = usedWater

Stutter ==
  /\ small'    = small
  /\ big'      = big
  /\ usedWater'= usedWater

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ FillBig
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall
  \/ Stutter

vars == <<small, big, usedWater>>

WaterAmountsInRange ==
  /\ small >= 0   /\ small <= SmallCap
  /\ big   >= 0   /\ big   <= BigCap

UsedWaterMonotonic ==
  /\ usedWater' >= usedWater

Safety == WaterAmountsInRange

EventuallyBig4 == <> (big = 4)

Liveness == EventuallyBig4

Spec == Init /\ [][Next]_vars

FullSpec == Spec /\ Safety
=============================================================================

MODULE DieHard
CONSTANTS SmallCap, BigCap
VARIABLES small, big, usedWater

Init ==
  /\ small = 0
  /\ big   = 0
  /\ usedWater = 0

FillSmall ==
  /\ small' = SmallCap
  /\ big'   = big
  /\ usedWater' = usedWater + SmallCap

EmptySmall ==
  /\ small' = 0
  /\ big'   = big
  /\ usedWater' = usedWater

FillBig ==
  /\ big'   = BigCap
  /\ small' = small
  /\ usedWater' = usedWater + BigCap

EmptyBig ==
  /\ big'   = 0
  /\ small' = small
  /\ usedWater' = usedWater

PourSmallToBig ==
  LET transfer == Min(small, BigCap - big) IN
  /\ small' = small - transfer
  /\ big'   = big + transfer
  /\ usedWater' = usedWater

PourBigToSmall ==
  LET transfer == Min(big, SmallCap - small) IN
  /\ big'   = big - transfer
  /\ small' = small + transfer
  /\ usedWater' = usedWater

Stutter ==
  /\ small'    = small
  /\ big'      = big
  /\ usedWater'= usedWater

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ FillBig
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall
  \/ Stutter

vars == <<small, big, usedWater>>

WaterAmountsInRange ==
  /\ small >= 0   /\ small <= SmallCap
  /\ big   >= 0   /\ big   <= BigCap

UsedWaterMonotonic ==
  /\ usedWater' >= usedWater

Safety == WaterAmountsInRange

EventuallyBig4 == <> (big = 4)

Liveness == EventuallyBig4

Spec == Init /\ [][Next]_vars
=============================================================================