------------------------------- MODULE DieHardTLC -------------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

-----------------------------------------------------------------------------
(* TLC registers: 1 = water usage counter, 2 = big-jug-has-4 flag          *)

WaterReg == 1
FoundReg == 2

ASSUME TLCSet(WaterReg, 0) /\ TLCSet(FoundReg, FALSE)

-----------------------------------------------------------------------------

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = SmallCap
             /\ big' = big
             /\ TLCSet(WaterReg, TLCGet(WaterReg) + (SmallCap - small))

FillBig == /\ big' = BigCap
           /\ small' = small
           /\ TLCSet(WaterReg, TLCGet(WaterReg) + (BigCap - big))

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

SmallToBig == /\ big'   = Min(big + small, BigCap)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, SmallCap)
              /\ big'   = big - (small' - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants                                                        *)

Inv == TypeOK

NotSolved == big /= 4

-----------------------------------------------------------------------------
(* TLC-specific instrumentation                                             *)

\* State constraint that records whether a state with big = 4 is reachable.
RecordSolution == (big = 4) => TLCSet(FoundReg, TRUE)

\* Inspect current statistics during model checking.
StatsInv == /\ TLCGet("level") \in Nat
            /\ TLCGet("stats").distinct >= 0
            /\ TLCGet("stats").generated >= TLCGet("stats").distinct
            /\ TLCGet(WaterReg) >= 0

\* The state space contains a state where the big jug holds 4 gallons.
SolutionExists == TLCGet(FoundReg) = TRUE

\* Expected statistics after model checking completes.
ExpectedStats == /\ TLCGet("stats").distinct = 16
                 /\ TLCGet("stats").generated >= 16
                 /\ TLCGet("stats").queue = 0

PostCondition == /\ SolutionExists
                 /\ ExpectedStats
                 /\ PrintT(<<"water used", TLCGet(WaterReg)>>)

=============================================================================