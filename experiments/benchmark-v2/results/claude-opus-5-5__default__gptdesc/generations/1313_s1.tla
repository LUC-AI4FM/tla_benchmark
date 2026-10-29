---------------------------- MODULE DieHardTLC ----------------------------
EXTENDS Naturals, TLC

(***************************************************************************)
(* The Die Hard water-jug problem: a small jug of capacity 3 and a big jug *)
(* of capacity 5.  TLC-specific operators (TLCGet / TLCSet) are used to    *)
(* track a custom counter of water usage, to record whether a state with   *)
(* 4 gallons in the big jug was reached, and to inspect model-checking     *)
(* statistics after model checking completes.                              *)
(*                                                                         *)
(* TLC registers used:                                                     *)
(*   1 : total amount of water drawn from the tap (water usage counter)    *)
(*   2 : TRUE iff a state with big = 4 has been encountered                *)
(***************************************************************************)

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

---------------------------------------------------------------------------
Init == /\ small = 0
        /\ big   = 0
        /\ TLCSet(1, 0)
        /\ TLCSet(2, FALSE)

FillSmallJug  == /\ small' = SmallCap
                 /\ big'   = big
                 /\ TLCSet(1, TLCGet(1) + (SmallCap - small))

FillBigJug    == /\ big'   = BigCap
                 /\ small' = small
                 /\ TLCSet(1, TLCGet(1) + (BigCap - big))

EmptySmallJug == /\ small' = 0
                 /\ big'   = big

EmptyBigJug   == /\ big'   = 0
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

---------------------------------------------------------------------------
(* Invariant used to record (via TLC register 2) whether a state with      *)
(* big = 4 exists in the state space.  It always evaluates to TRUE.        *)
RecordBigIsFour == TLCSet(2, IF big = 4 THEN TRUE ELSE TLCGet(2))

(* Classic invariant whose violation yields the solution trace.            *)
NotSolved == big # 4

(* Sanity invariant on the water usage counter.                            *)
WaterUsageOK == TLCGet(1) \in Nat

---------------------------------------------------------------------------
(* Predicates to be checked after model checking (e.g. as a POSTCONDITION). *)

(* The state space contains a state where the big jug holds 4 gallons.     *)
FoundBigIsFour == TLCGet(2) = TRUE

(* Expected statistics: 16 distinct reachable states, no states left in    *)
(* the queue, and at least as many generated states as distinct ones.      *)
StatsExpectation ==
    LET stats == TLCGet("stats")
    IN  /\ stats.distinct = 16
        /\ stats.queue = 0
        /\ stats.generated >= stats.distinct

PostCondition == FoundBigIsFour /\ StatsExpectation

=============================================================================