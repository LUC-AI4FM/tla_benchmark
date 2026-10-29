------------------------------ MODULE DieHardTLA ------------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

-----------------------------------------------------------------------------
(* TLC registers:                                                           *)
(*   1 : custom counter of water usage (gallons drawn from the faucet)      *)
(*   2 : flag set to TRUE once a state with big = 4 has been seen           *)
-----------------------------------------------------------------------------

UsedWater == 1
FoundFour == 2

ASSUME TLCSet(UsedWater, 0)
ASSUME TLCSet(FoundFour, FALSE)

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

Init == /\ small = 0
        /\ big = 0

FillSmallJug == /\ small' = SmallCap
                /\ big' = big
                /\ TLCSet(UsedWater, TLCGet(UsedWater) + (SmallCap - small))

FillBigJug == /\ big' = BigCap
              /\ small' = small
              /\ TLCSet(UsedWater, TLCGet(UsedWater) + (BigCap - big))

EmptySmallJug == /\ small' = 0
                 /\ big' = big

EmptyBigJug == /\ big' = 0
               /\ small' = small

SmallToBig == /\ big'   = Min(big + small, BigCap)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, SmallCap)
              /\ big'   = big - (small' - small)

Next == \/ FillSmallJug
        \/ FillBigJug
        \/ EmptySmallJug
        \/ EmptyBigJug
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariant: types are preserved.                                   *)
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK

-----------------------------------------------------------------------------
(* The classic "invariant" whose violation exhibits a solution.             *)
-----------------------------------------------------------------------------
NotSolved == big # 4

-----------------------------------------------------------------------------
(* Invariant used only for its side effect: records in a TLC register that  *)
(* a state with big = 4 belongs to the state space. Always evaluates TRUE.  *)
-----------------------------------------------------------------------------
RecordFour == (big = 4) => TLCSet(FoundFour, TRUE)

-----------------------------------------------------------------------------
(* Inspection of model-checking statistics.                                 *)
-----------------------------------------------------------------------------
Stats == TLCGet("stats")

ReachableFour == TLCGet(FoundFour) = TRUE

ExpectedDistinct == 16

StatsOK == /\ Stats.distinct = ExpectedDistinct
           /\ Stats.generated >= Stats.distinct
           /\ Stats.diameter >= 1

WaterUsageOK == TLCGet(UsedWater) >= 0

PostCondition == /\ ReachableFour
                 /\ StatsOK
                 /\ WaterUsageOK
                 /\ PrintT(<<"stats", Stats, "water", TLCGet(UsedWater)>>)

=============================================================================