---------------------------- MODULE DieHardCounts ----------------------------
EXTENDS Naturals, TLC

(***************************************************************************)
(* Two-jug water-pouring puzzle: a small jug of capacity 3 and a big jug   *)
(* of capacity 5. There is an unlimited source and an unlimited sink.      *)
(***************************************************************************)

SmallCap == 3
BigCap   == 5

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

(***************************************************************************)
(* TLC registers used for instrumentation:                                 *)
(*   1 : number of transitions that change the contents of a jug           *)
(*   2 : total water drawn from the source over the exploration            *)
(*   3 : number of times a state with big = 4 was encountered              *)
(***************************************************************************)

Init == /\ small = 0
        /\ big = 0
        /\ TLCSet(1, 0)
        /\ TLCSet(2, 0)
        /\ TLCSet(3, 0)

FillSmall  == /\ small' = SmallCap
              /\ big' = big

FillBig    == /\ big' = BigCap
              /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig   == /\ big' = 0
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

(***************************************************************************)
(* Safety-style predicate: the larger jug contains exactly 4 units.        *)
(***************************************************************************)
HasFour == big = 4

(***************************************************************************)
(* Possibility instrumentation: always TRUE, but records visits to states *)
(* in which HasFour holds.                                                 *)
(***************************************************************************)
_POSSIBLE == IF HasFour
               THEN TLCSet(3, TLCGet(3) + 1)
               ELSE TRUE

(***************************************************************************)
(* Water drawn from the source by a transition: total water only grows    *)
(* through a fill operation, so the increase in total water is the amount *)
(* drawn.                                                                  *)
(***************************************************************************)
Drawn == IF (small' + big') > (small + big)
           THEN (small' + big') - (small + big)
           ELSE 0

(***************************************************************************)
(* Observable "pour or change" action: counts every transition that       *)
(* changes the contents of either jug and accumulates water drawn.        *)
(* Always TRUE, so it never restricts exploration.                         *)
(***************************************************************************)
PourAction == IF (small' # small \/ big' # big)
                THEN /\ TLCSet(1, TLCGet(1) + 1)
                     /\ TLCSet(2, TLCGet(2) + Drawn)
                ELSE TRUE

(***************************************************************************)
(* Expected results of the exploration.                                    *)
(***************************************************************************)
ExpectedGenerated == 97
ExpectedDistinct  == 16
ExpectedDiameter  == 8
ExpectedDrawn     == 64
ExpectedAverage   == 4

PossibleCounts ==
    LET stats == TLCGet("stats")
    IN  /\ stats.generated = ExpectedGenerated
        /\ stats.distinct  = ExpectedDistinct
        /\ stats.diameter  = ExpectedDiameter
        /\ TLCGet(2) = ExpectedDrawn
        /\ (TLCGet(2) \div stats.distinct) = ExpectedAverage

=============================================================================