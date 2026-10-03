---- MODULE DieHard ----
EXTENDS Naturals, TLC

(*
  Classic Die Hard water-jug problem:
  - Two jugs with capacities 3 and 5.
  - State: amounts of water in the small and big jugs.
  - Actions: fill, empty, pour between jugs.
  - Temporal spec: Init /\ [][Next]_vars (stuttering-closed).
  - TLC-specific operators are used to keep a custom counter of
    the number of actions taken and the amount of water drawn
    from the faucet during fills.
*)

(*
  Fixed capacities (no CONSTANT parameters needed for this instance).
*)
SmallCap == 3
BigCap   == 5

VARIABLES small, big

vars == << small, big >>

(*
  Helper: force evaluation of an expression (e.g., TLCSet) while
  contributing TRUE to a formula.
*)
TLCDo(e) == e = e

(*
  Arithmetic minimum of two integers.
*)
Min2(a, b) == IF a <= b THEN a ELSE b

(*
  State and type constraints.
*)
TypeInv == /\ small \in 0..SmallCap
          /\ big \in 0..BigCap

Init ==
  /\ small = 0
  /\ big = 0
  /\ TLCDo(TLCSet("ActionCount", 0))
  /\ TLCDo(TLCSet("WaterUsed", 0))

(*
  Primitive actions.
*)
FillSmall ==
  /\ small < SmallCap
  /\ small' = SmallCap
  /\ big' = big

FillBig ==
  /\ big < BigCap
  /\ big' = BigCap
  /\ small' = small

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big' = big

EmptyBig ==
  /\ big > 0
  /\ big' = 0
  /\ small' = small

PourSmallToBig ==
  LET delta == Min2(small, BigCap - big)
  IN  /\ delta > 0
      /\ small' = small - delta
      /\ big' = big + delta

PourBigToSmall ==
  LET delta == Min2(big, SmallCap - small)
  IN  /\ delta > 0
      /\ big' = big - delta
      /\ small' = small + delta

(*
  Next-state relation:
  - Any one of the primitive actions occurs.
  - TLC bookkeeping increments:
      - "ActionCount" (counts transitions explored)
      - "WaterUsed" (adds faucet-drawn water for fill actions only)
*)
Next ==
  LET A1 == FillSmall
      A2 == FillBig
      A3 == EmptySmall
      A4 == EmptyBig
      A5 == PourSmallToBig
      A6 == PourBigToSmall
      Act == A1 \/ A2 \/ A3 \/ A4 \/ A5 \/ A6
      Faucet == IF A1 THEN SmallCap - small
                ELSE IF A2 THEN BigCap - big
                ELSE 0
  IN  /\ Act
      /\ TLCDo(TLCSet("ActionCount", TLCGet("ActionCount") + 1))
      /\ TLCDo(TLCSet("WaterUsed", TLCGet("WaterUsed") + Faucet))

Spec == Init /\ [][Next]_vars

(*
  Predicates intended for model-checking/inspection.
*)
Goal == big = 4
ReachGoal == <> Goal

ActionCount == TLCGet("ActionCount")
WaterUsed   == TLCGet("WaterUsed")

ActionCountPositive == ActionCount > 0
WaterUsedIsNat      == WaterUsed \in Nat

====