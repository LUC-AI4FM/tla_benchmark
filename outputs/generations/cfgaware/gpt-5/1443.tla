---- MODULE SmallCycle ----
EXTENDS Naturals, TLC

VARIABLE x

Init ==
  x = 0

Next ==
  \/ /\ x = 2
     /\ x' = 0
  \/ /\ x # 2
     /\ x' = x + 1

Spec ==
  Init /\ [][Next]_x

(*
  Helper predicates:
  - pOne: state is 1
  - pDone: all work done at 2
  - pWrap: transition wraps from 2 back to 0 (action predicate)
*)
pOne ==
  x = 1

pDone ==
  x = 2

pWrap ==
  /\ x = 2
  /\ x' = 0

(*
  TLC-specific coverage check:
  Expects that:
   - state predicates pOne and pDone are each counted once
   - action predicate pWrap is counted once
  under TLC's named predicate coverage.
*)
CoverageCheck ==
  LET sp == TLCGet("statePredicates") IN
  LET ap == TLCGet("actionPredicates") IN
    Assert(sp["pOne"] = 1 /\ sp["pDone"] = 1 /\ ap["pWrap"] = 1,
           "Coverage counts mismatch for pOne, pDone, or pWrap")

====