---- MODULE DieHard ----
EXTENDS Naturals, TLC

(*
  Classic Die Hard water-jug puzzle:
  - small jug capacity: 3
  - big jug capacity:   5
  Goal: measure exactly 4 gallons in the big jug.
*)

CONSTANTS

(*
  Fixed capacities as definitions (not model constants).
*)
SmallCap == 3
BigCap   == 5

(*
  TLC register used for instrumentation: accumulates total gallons filled.
*)
RegId == 42

VARIABLES small, big

Vars == << small, big >>

Init ==
  /\ small = 0
  /\ big   = 0
  /\ TLC!TLCSet(RegId, 0) = 0

(*
  Actions
*)

FillSmall ==
  /\ small < SmallCap
  /\ small' = SmallCap
  /\ big'   = big
  /\ TLC!TLCSet(RegId, TLC!TLCGet(RegId) + (SmallCap - small))
     = TLC!TLCGet(RegId) + (SmallCap - small)

FillBig ==
  /\ big < BigCap
  /\ big'   = BigCap
  /\ small' = small
  /\ TLC!TLCSet(RegId, TLC!TLCGet(RegId) + (BigCap - big))
     = TLC!TLCGet(RegId) + (BigCap - big)

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big'   = big

EmptyBig ==
  /\ big > 0
  /\ big'   = 0
  /\ small' = small

SmallToBig ==
  LET t == Min(small, BigCap - big)
  IN /\ t > 0
     /\ small' = small - t
     /\ big'   = big + t

BigToSmall ==
  LET t == Min(big, SmallCap - small)
  IN /\ t > 0
     /\ big'   = big - t
     /\ small' = small + t

Next ==
  FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ SmallToBig
  \/ BigToSmall

(*
  State invariant and predicates
*)
TypeOK ==
  /\ 0 <= small /\ small <= SmallCap
  /\ 0 <= big   /\ big   <= BigCap

HasFour == big = 4

(*
  True on transitions where both jugs change simultaneously.
*)
PourAction == (small' # small) /\ (big' # big)

(*
  Stuttering-tolerant temporal specification
*)
Spec == Init /\ [][Next]_Vars

(*
  TLC post-run assertions over statistics and instrumentation.
  The total gallons counted via FillSmall and FillBig must be 128.
  Expected model stats:
    - generated states: 97
    - distinct states:  16
    - diameter:          8
*)
PostCondition ==
  TLC!PostCondition(
    /\ TLC!TLCGet("generated") = 97
    /\ TLC!TLCGet("distinct")  = 16
    /\ TLC!TLCGet("diameter")  = 8
    /\ TLC!TLCGet(RegId)       = 128
  )

(*
  _POSSIBLE annotation: expected reachability counts recorded here.
*)
HasFour_POSSIBLE  == 8
PourAction_POSSIBLE == 14

PossibleCounts ==
  /\ HasFour_POSSIBLE  = 8
  /\ PourAction_POSSIBLE = 14

====