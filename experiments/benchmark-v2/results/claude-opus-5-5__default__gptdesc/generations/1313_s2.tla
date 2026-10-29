---------------------------- MODULE DieHardTLC ----------------------------
EXTENDS Naturals, TLC

VARIABLES small, big

vars == <<small, big>>

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Min(m, n) == IF m < n THEN m ELSE n

(***************************************************************************)
(* TLC register 1 is a custom counter of the total water used (filled in   *)
(* from the tap). TLC register 2 records whether a state in which the big  *)
(* jug holds 4 gallons has been seen during model checking.                *)
(***************************************************************************)
Init == /\ small = 0
        /\ big = 0
        /\ TLCSet(1, 0)
        /\ TLCSet(2, FALSE)

FillSmallJug  == /\ small' = 3
                 /\ big' = big
                 /\ TLCSet(1, TLCGet(1) + (3 - small))

FillBigJug    == /\ big' = 5
                 /\ small' = small
                 /\ TLCSet(1, TLCGet(1) + (5 - big))

EmptySmallJug == /\ small' = 0
                 /\ big' = big

EmptyBigJug   == /\ big' = 0
                 /\ small' = small

SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3)
              /\ big'   = big - (small' - small)

Next == \/ FillSmallJug
        \/ FillBigJug
        \/ EmptySmallJug
        \/ EmptyBigJug
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Classic "invariant" whose violation exhibits a solution to the puzzle.  *)
(***************************************************************************)
NotSolved == big # 4

(***************************************************************************)
(* An invariant that always holds (TLCSet returns TRUE) but records in     *)
(* register 2 whether a state with big = 4 has been encountered.           *)
(***************************************************************************)
RecordBigIsFour == TLCSet(2, IF big = 4 THEN TRUE ELSE TLCGet(2))

(***************************************************************************)
(* Inspection of TLC statistics during model checking.                     *)
(***************************************************************************)
WaterUsed == TLCGet(1)

StatsOK == /\ TLCGet("level") \in Nat
           /\ TLCGet("distinct") \in Nat
           /\ WaterUsed \in Nat

(***************************************************************************)
(* Post-condition evaluated after model checking completes: the state      *)
(* space contains a state where the big jug has 4 gallons, the expected    *)
(* number of distinct states was found, and the queue is exhausted.        *)
(***************************************************************************)
StateSpaceHasBigFour == TLCGet(2) = TRUE

ExpectedCounts ==
    LET stats == TLCGet("stats")
    IN  /\ stats.distinct = 16
        /\ stats.generated >= stats.distinct
        /\ stats.queue = 0

PostCondition == /\ StateSpaceHasBigFour
                 /\ ExpectedCounts

THEOREM Spec => []TypeOK
=============================================================================