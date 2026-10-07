------------------------------- MODULE DieHardJugs -------------------------------

EXTENDS Naturals, TLC

(*
  Classic Die Hard water-jug problem with a 3-gallon (small) and a 5-gallon (big) jug.
  State variables are the current amounts of water in each jug. Actions model filling,
  emptying, and pouring between the jugs. The temporal specification is an initial
  condition conjoined with a stuttering-closed next-state relation. The spec also
  provides TLC-specific instrumentation for inspecting model-checking statistics
  and a custom counter that accumulates total gallons of water moved by actions.
*)

CONSTANTS SmallCap, BigCap

(*
  Fix the capacities to 3 and 5 as per the problem statement.
  A TLC model may omit or override these ASSUMEs, but this module intends 3 and 5.
*)
ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big, usage

Vars == << small, big, usage >>

(*
  Helper minimum operator.
*)
Min(m, n) == IF m <= n THEN m ELSE n

(*
  Initial state: both jugs empty; custom usage counter is zero.
*)
Init ==
  /\ small = 0
  /\ big   = 0
  /\ usage = 0

(*
  Safety/type invariant: amounts remain within jug capacities; usage is a natural.
*)
TypeInv ==
  /\ small \in 0..SmallCap
  /\ big   \in 0..BigCap
  /\ usage \in Nat

(*
  Actions:
    - FillSmall / FillBig: fill a jug to capacity.
    - EmptySmall / EmptyBig: empty a jug.
    - PourSmallToBig / PourBigToSmall: pour until source empty or destination full.
  The 'usage' counter increases by the gallons moved (filled, emptied, or poured).
*)
FillSmall ==
  /\ small < SmallCap
  /\ small' = SmallCap
  /\ big'   = big
  /\ usage' = usage + (SmallCap - small)

FillBig ==
  /\ big < BigCap
  /\ small' = small
  /\ big'   = BigCap
  /\ usage' = usage + (BigCap - big)

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big'   = big
  /\ usage' = usage + small

EmptyBig ==
  /\ big > 0
  /\ small' = small
  /\ big'   = 0
  /\ usage' = usage + big

PourSmallToBig ==
  /\ small > 0
  /\ big < BigCap
  /\ LET d == Min(small, BigCap - big)
     IN /\ small' = small - d
        /\ big'   = big + d
        /\ usage' = usage + d

PourBigToSmall ==
  /\ big > 0
  /\ small < SmallCap
  /\ LET d == Min(big, SmallCap - small)
     IN /\ small' = small + d
        /\ big'   = big - d
        /\ usage' = usage + d

Next ==
  FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

(*
  Stuttering-closed temporal specification.
*)
Spec == Init /\ [][Next]_Vars

(*
  State predicate for the goal “big jug has 4 gallons”.
*)
BigHas4 == big = 4

(*
  Liveness-style reachability predicate intended for TLC PROPERTY checking:
  Does every behavior eventually reach a state with the big jug at 4 gallons?
  (Note: This is stronger than mere existence in the reachable state graph.)
*)
FourIsReachable == <> BigHas4

(*
  TLC-specific instrumentation:
    - MCStates, MCDistinct, MCActions are intended to expose TLC’s bookkeeping.
      The exact keys are TLC engine-specific; these are provided for post-check inspection.
    - CountExpectations encodes simple sanity checks on the discovered state graph.
  These are not included in Spec; they can be evaluated in the TLC model after checking.
*)
MCStates    == TLCGet("states")
MCDistinct  == TLCGet("distinctStates")
MCActions   == TLCGet("actions")

CountExpectations ==
  /\ MCStates    >= 1
  /\ MCDistinct  >= 1
  /\ MCActions   >= 1

=============================================================================