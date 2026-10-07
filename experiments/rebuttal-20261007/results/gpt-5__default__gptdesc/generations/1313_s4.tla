----------------------------- MODULE DieHard -----------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES s, b, waterUsed

vars == << s, b, waterUsed >>

Min(a, c) == IF a <= c THEN a ELSE c

TypeInv ==
  /\ s \in 0..SmallCap
  /\ b \in 0..BigCap
  /\ waterUsed \in Nat

Init ==
  /\ s = 0
  /\ b = 0
  /\ waterUsed = 0

TrackWater(v) == TLCSet("waterUsed", v) = v

FillSmall ==
  /\ s < SmallCap
  /\ s' = SmallCap
  /\ b' = b
  /\ waterUsed' = waterUsed + (SmallCap - s)
  /\ TrackWater(waterUsed')

EmptySmall ==
  /\ s > 0
  /\ s' = 0
  /\ b' = b
  /\ waterUsed' = waterUsed
  /\ TrackWater(waterUsed')

FillBig ==
  /\ b < BigCap
  /\ b' = BigCap
  /\ s' = s
  /\ waterUsed' = waterUsed + (BigCap - b)
  /\ TrackWater(waterUsed')

EmptyBig ==
  /\ b > 0
  /\ b' = 0
  /\ s' = s
  /\ waterUsed' = waterUsed
  /\ TrackWater(waterUsed')

PourSmallToBig ==
  LET pour == Min(s, BigCap - b)
  IN
  /\ pour > 0
  /\ s' = s - pour
  /\ b' = b + pour
  /\ waterUsed' = waterUsed
  /\ TrackWater(waterUsed')

PourBigToSmall ==
  LET pour == Min(b, SmallCap - s)
  IN
  /\ pour > 0
  /\ b' = b - pour
  /\ s' = s + pour
  /\ waterUsed' = waterUsed
  /\ TrackWater(waterUsed')

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ FillBig
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

Spec == Init /\ [][Next]_vars

(*
  Safety invariants intended for TLC checking.
*)
Inv ==
  /\ TypeInv

(*
  Goal predicate (big jug has exactly 4 gallons).
  This is intended to be inspected in the reachable state space or
  used as a temporal property like <>Goal in a separate model check.
*)
Goal == b = 4

(*
  TLC-specific statistics and predicates intended for post-run inspection.
  The concrete keys are evaluated by TLC at run time; these definitions
  are provided for convenience in models or assertions.
*)
NumStates          == TLCGet("numStates")
NumDistinctStates  == TLCGet("numDistinctStates")
NumTransitions     == TLCGet("numTransitions")
ObservedWaterUsed  == TLCGet("waterUsed")

CONSTANTS ExpectedDistinctStates, ExpectedTransitions

StatsOK ==
  /\ NumDistinctStates = ExpectedDistinctStates
  /\ NumTransitions    >= ExpectedTransitions
============================================================================