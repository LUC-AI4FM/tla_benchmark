----------------------------- MODULE DieHard -----------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

(*
  Fixed capacities for the classic Die Hard water-jug problem:
  SmallCap = 3, BigCap = 5
*)
ASSUME /\ SmallCap = 3
       /\ BigCap = 5
       /\ SmallCap \in Nat
       /\ BigCap \in Nat
       /\ SmallCap < BigCap

VARIABLES s, b, W

Vars == << s, b, W >>

Min(a, c) == IF a < c THEN a ELSE c

(*
  TLC-side-effect helpers
*)
Inc(name, val) == TLCSet(name, TLCGet(name) + val)

Init ==
  /\ s = 0
  /\ b = 0
  /\ W = 0
  /\ LET _ == TLCSet("FillCount", 0) IN TRUE
  /\ LET _ == TLCSet("EmptyCount", 0) IN TRUE
  /\ LET _ == TLCSet("PourCount", 0) IN TRUE
  /\ LET _ == TLCSet("StateCount", 1) IN TRUE

(*
  Actions:
  - Fill adds water from the faucet (increasing W).
  - Empty discards water to the drain (increasing W).
  - Pour transfers water between jugs (W unchanged).
*)

FillSmall ==
  /\ s < SmallCap
  /\ s' = SmallCap
  /\ b' = b
  /\ W' = W + (SmallCap - s)
  /\ LET _ == Inc("FillCount", 1) IN TRUE

FillBig ==
  /\ b < BigCap
  /\ b' = BigCap
  /\ s' = s
  /\ W' = W + (BigCap - b)
  /\ LET _ == Inc("FillCount", 1) IN TRUE

EmptySmall ==
  /\ s > 0
  /\ s' = 0
  /\ b' = b
  /\ W' = W + s
  /\ LET _ == Inc("EmptyCount", 1) IN TRUE

EmptyBig ==
  /\ b > 0
  /\ b' = 0
  /\ s' = s
  /\ W' = W + b
  /\ LET _ == Inc("EmptyCount", 1) IN TRUE

PourSmallToBig ==
  /\ s > 0
  /\ b < BigCap
  /\ LET a == Min(s, BigCap - b) IN
       /\ s' = s - a
       /\ b' = b + a
       /\ W' = W
  /\ LET _ == Inc("PourCount", 1) IN TRUE

PourBigToSmall ==
  /\ b > 0
  /\ s < SmallCap
  /\ LET a == Min(b, SmallCap - s) IN
       /\ b' = b - a
       /\ s' = s + a
       /\ W' = W
  /\ LET _ == Inc("PourCount", 1) IN TRUE

Next ==
  /\ ( FillSmall
     \/ FillBig
     \/ EmptySmall
     \/ EmptyBig
     \/ PourSmallToBig
     \/ PourBigToSmall )
  /\ LET _ == Inc("StateCount", 1) IN TRUE

Spec == Init /\ [][Next]_Vars

(*
  Safety invariants
*)
TypeOK ==
  /\ s \in 0..SmallCap
  /\ b \in 0..BigCap
  /\ W \in Nat

(*
  Goal predicate: intended to check the state space contains a state
  with 4 gallons in the big jug (b = 4).
*)
Goal == b = 4

(*
  A liveness-style predicate one might ask TLC to check to witness reachability.
  Note: <>Goal requires that along all behaviors, Goal is eventually reached;
  it is stronger than mere existence of a reachable state.
*)
EventuallyGoal == <>Goal

(*
  TLC-specific post-check predicates to inspect counters after model checking.
  These are constant-level expressions TLC can evaluate once the model has been explored.
*)
ActionCountsOK ==
  /\ TLCGet("FillCount") >= 0
  /\ TLCGet("EmptyCount") >= 0
  /\ TLCGet("PourCount") >= 0

SawAnyAction ==
  TLCGet("FillCount") + TLCGet("EmptyCount") + TLCGet("PourCount") > 0

StateCountingOK ==
  TLCGet("StateCount") >= 1
=============================================================================