MODULE DieHardWaterJug
EXTENDS Naturals, TLC

CONSTANTS SMALL_CAP, BIG_CAP

VARIABLES smallJug, bigJug, usage

vars == <<smallJug, bigJug, usage>>

(* State type *)
State == [smallJug: 0..SMALL_CAP,
          bigJug: 0..BIG_CAP,
          usage: Nat]

Init ==
    /\ smallJug = 0
    /\ bigJug = 0
    /\ usage = 0

FillSmall ==
    /\ smallJug' = SMALL_CAP
    /\ bigJug' = bigJug
    /\ usage' = usage + 1

FillBig ==
    /\ bigJug' = BIG_CAP
    /\ smallJug' = smallJug
    /\ usage' = usage + 1

EmptySmall ==
    /\ smallJug' = 0
    /\ bigJug' = bigJug
    /\ usage' = usage

EmptyBig ==
    /\ bigJug' = 0
    /\ smallJug' = smallJug
    /\ usage' = usage

PourSmallToBig ==
    LET transfer == Min(smallJug, BIG_CAP - bigJug) IN
    /\ smallJug' = smallJug - transfer
    /\ bigJug' = bigJug + transfer
    /\ usage' = usage

PourBigToSmall ==
    LET transfer == Min(bigJug, SMALL_CAP - smallJug) IN
    /\ bigJug' = bigJug - transfer
    /\ smallJug' = smallJug + transfer
    /\ usage' = usage

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ PourSmallToBig
    \/ PourBigToSmall

(* Safety invariant *)
Inv == 
    /\ smallJug <= SMALL_CAP
    /\ bigJug <= BIG_CAP
    /\ usage >= 0

Spec ==
    Init /\ [][Next]_vars

Safety == []Inv

Liveness == <> (bigJug = 4)

(* TLC statistics predicates *)
Big4Exists == <> (bigJug = 4)
StateCount == TLCStats.states
TransitionCount == TLCStats.transitions

StateCountExpectation == StateCount >= 10
TransitionCountExpectation == TransitionCount >= 15

END MODULE