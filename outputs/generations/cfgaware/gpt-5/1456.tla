------------------------------- MODULE TinyStateMachine -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(*
  Two-variable state machine over x and y.
  - y stays constant across steps.
  - x' is constrained to be a subset of y' (hence of y).
  - FullSet checks x = {1,2,3}.
  - GainThree checks that element 3 is gained in a transition (from not in x to in x').
  - Uses TLCGet to probe exploration metadata and assert expected counts if available.
*)

VARIABLES x, y

S == {1, 2, 3}

Init ==
  /\ y \in { S }
  /\ x \in SUBSET y

Next ==
  /\ y' = y
  /\ x' \in SUBSET y'

TypeOK ==
  /\ x \subseteq y
  /\ y = S

FullSet ==
  x = S

GainThree ==
  /\ ~(3 \in x)
  /\ 3 \in x'

DistinctStatesExpected ==
  Cardinality(SUBSET S)

FullSetCountExpected ==
  Cardinality({ z \in SUBSET S : z = S })

GainThreeCountExpected ==
  Cardinality({ p \in (SUBSET S) \X (SUBSET S) : ~(3 \in p[1]) /\ 3 \in p[2] })

TLCCountsOK ==
  /\ LET ds == TLCGet("distinctStates") IN
       IF ds \in Nat
         THEN Assert(ds = DistinctStatesExpected, "distinctStates mismatch")
         ELSE TRUE
  /\ LET fs == TLCGet("FullSet") IN
       IF fs \in Nat
         THEN Assert(fs = FullSetCountExpected, "FullSet count mismatch")
         ELSE TRUE
  /\ LET gt == TLCGet("GainThree") IN
       IF gt \in Nat
         THEN Assert(gt = GainThreeCountExpected, "GainThree count mismatch")
         ELSE TRUE

Inv ==
  /\ TypeOK
  /\ TLCCountsOK
=============================================================================