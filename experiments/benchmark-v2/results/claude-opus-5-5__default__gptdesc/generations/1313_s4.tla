------------------------------ MODULE DieHardTLC ------------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big

vars == << small, big >>

Min(m, n) == IF m < n THEN m ELSE n

-----------------------------------------------------------------------------
(* Registers used during model checking:                                  *)
(*   1 : custom counter of the total water used by fill actions            *)
(*   2 : flag recording whether a state with big = 4 has been seen         *)
-----------------------------------------------------------------------------

ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, FALSE)

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

Init == /\ small = 0
        /\ big = 0

FillSmallJug == /\ small' = SmallCap
                /\ big' = big
                /\ TLCSet(1, TLCGet(1) + (SmallCap - small))

FillBigJug == /\ big' = BigCap
              /\ small' = small
              /\ TLCSet(1, TLCGet(1) + (BigCap - big))

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
(* Invariants                                                              *)
-----------------------------------------------------------------------------

\* Violated exactly when TLC finds a solution to the puzzle.
NotSolved == big # 4

\* Records (as a side effect) that a state with big = 4 was reached.
\* Always TRUE, so it can be checked as an invariant without failing.
RecordFour == IF big = 4 THEN TLCSet(2, TRUE) ELSE TRUE

\* Inspection of the custom water-usage counter and TLC statistics.
WaterUsageNonNegative == TLCGet(1) >= 0

LevelBounded == TLCGet("level") >= 1

-----------------------------------------------------------------------------
(* Post-condition checked after model checking completes                   *)
-----------------------------------------------------------------------------

FoundFour == TLCGet(2) = TRUE

StatsExpectation ==
    /\ TLCGet("stats").distinct = 16
    /\ TLCGet("stats").generated >= TLCGet("stats").distinct
    /\ TLCGet("stats").diameter >= 1

PostCondition == /\ FoundFour
                 /\ StatsExpectation
                 /\ TLCGet(1) > 0

=============================================================================