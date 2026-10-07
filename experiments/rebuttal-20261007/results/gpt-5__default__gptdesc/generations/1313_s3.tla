------------------------------ MODULE DieHard ------------------------------

EXTENDS Naturals, TLC

CONSTANTS
  SmallCap, BigCap,
  EXPECTED_STATES, EXPECTED_DISTINCT, EXPECTED_TRANSITIONS

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big, WaterUsed

vars == << small, big, WaterUsed >>

Init ==
  /\ small = 0
  /\ big = 0
  /\ WaterUsed = 0

FillSmall ==
  /\ small < SmallCap
  /\ small' = SmallCap
  /\ big' = big
  /\ WaterUsed' = WaterUsed + (SmallCap - small)

FillBig ==
  /\ big < BigCap
  /\ big' = BigCap
  /\ small' = small
  /\ WaterUsed' = WaterUsed + (BigCap - big)

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big' = big
  /\ WaterUsed' = WaterUsed + small

EmptyBig ==
  /\ big > 0
  /\ big' = 0
  /\ small' = small
  /\ WaterUsed' = WaterUsed + big

PourSmallToBig ==
  /\ small > 0
  /\ big < BigCap
  /\ LET space == BigCap - big
         move  == IF small <= space THEN small ELSE space
     IN /\ small' = small - move
        /\ big' = big + move
        /\ WaterUsed' = WaterUsed

PourBigToSmall ==
  /\ big > 0
  /\ small < SmallCap
  /\ LET space == SmallCap - small
         move  == IF big <= space THEN big ELSE space
     IN /\ big' = big - move
        /\ small' = small + move
        /\ WaterUsed' = WaterUsed

Next ==
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

Spec ==
  Init /\ [][Next]_vars

(*
  Safety invariants (state properties)
*)
TypeInv ==
  /\ small \in 0..SmallCap
  /\ big \in 0..BigCap
  /\ WaterUsed \in Nat

(*
  Liveness property expressing that there exists a reachable state
  where the big jug has 4 gallons.
*)
HasFourState == big = 4
ReachFour == <> HasFourState

(*
  TLC-specific statistics and post-run expectations.
  These are intended to be inspected after model checking.
*)
TotalStates == TLCGet("states")
DistinctStates == TLCGet("distinct")
Transitions == TLCGet("transitions")
Diameter == TLCGet("diameter")

StatsMeetExpectations ==
  /\ TotalStates = EXPECTED_STATES
  /\ DistinctStates = EXPECTED_DISTINCT
  /\ Transitions = EXPECTED_TRANSITIONS

=============================================================================