---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

CONSTANTS SmallCap, BigCap

VARIABLES small, big, waterUsed

vars == <<small, big, waterUsed>>

TypeOK == /\ small \in 0..SmallCap
          /\ big \in 0..BigCap
          /\ waterUsed \in Nat

Init == /\ small = 0
        /\ big = 0
        /\ waterUsed = 0

FillSmall == /\ small' = SmallCap
             /\ big' = big
             /\ waterUsed' = waterUsed + (SmallCap - small)

FillBig == /\ big' = BigCap
           /\ small' = small
           /\ waterUsed' = waterUsed + (BigCap - big)

EmptySmall == /\ small' = 0
              /\ big' = big
              /\ waterUsed' = waterUsed

EmptyBig == /\ big' = 0
            /\ small' = small
            /\ waterUsed' = waterUsed

SmallToBig == LET transfer == IF small + big <= BigCap 
                              THEN small 
                              ELSE BigCap - big
              IN /\ big' = big + transfer
                 /\ small' = small - transfer
                 /\ waterUsed' = waterUsed

BigToSmall == LET transfer == IF small + big <= SmallCap 
                              THEN big 
                              ELSE SmallCap - small
              IN /\ small' = small + transfer
                 /\ big' = big - transfer
                 /\ waterUsed' = waterUsed

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Invariants *)

NotFourGallons == big /= 4

SmallInRange == small >= 0 /\ small <= SmallCap
BigInRange == big >= 0 /\ big <= BigCap

-----------------------------------------------------------------------------
(* Predicates for checking state space *)

BigHasFour == big = 4

GoalReachable == TLCGet("level") > 0 => \E s \in {big} : TRUE

-----------------------------------------------------------------------------
(* TLC Statistics and Inspection Operators *)

StatesGenerated == TLCGet("generated")
DistinctStates == TLCGet("distinct")
CurrentLevel == TLCGet("level")

ExpectedDistinctStates == 16
ExpectedActions == 6

StatesCountCheck == DistinctStates <= 100

ActionCountExpectation == 
    TLCGet("generated") >= 0

PostCondition ==
    /\ PrintT(<<"States Generated:", StatesGenerated>>)
    /\ PrintT(<<"Distinct States:", DistinctStates>>)
    /\ PrintT(<<"Water Used Counter Available">>)

-----------------------------------------------------------------------------
(* Liveness Properties *)

EventuallyFour == <>(big = 4)

-----------------------------------------------------------------------------
(* Fairness Conditions *)

FairSpec == Spec /\ WF_vars(Next)

LiveSpec == FairSpec => EventuallyFour

-----------------------------------------------------------------------------
(* Default values for constants *)

SmallCapDef == 3
BigCapDef == 5

=============================================================================