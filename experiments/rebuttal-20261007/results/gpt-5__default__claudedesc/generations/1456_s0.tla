----------------------------- MODULE SubsetPrimeTest -----------------------------

EXTENDS Naturals, TLC

VARIABLES x, y

vars == << x, y >>

Init ==
  /\ x \in SUBSET {1, 2}
  /\ y = {1, 2, 3}

Next ==
  /\ y' = y
  /\ x' \subseteq y'

Spec ==
  Init /\ [][Next]_vars

(*
  Safety invariants to be checked by TLC
*)
TypeOK ==
  x \subseteq {1, 2, 3}

Inv ==
  /\ ENABLED (x' \subseteq {1})
  /\ y = {1, 2, 3}

(*
  Predicates for TLC's POSSIBLE tracking
*)
FullSet ==
  x = {1, 2, 3}

GainThree ==
  /\ ~(3 \in x)
  /\  (3 \in x')

(*
  Postcondition for POSSIBLE counts (harness-provided)
*)
ASSUME NEW CardinalityOfStates(_)
ASSUME NEW CardinalityOfActions(_)

_POSSIBLE ==
  [ states  |-> { "FullSet" }
  , actions |-> { "GainThree" }
  ]

PossibleCounts ==
  /\ CardinalityOfStates("FullSet")  = 8
  /\ CardinalityOfActions("GainThree") = 16

=============================================================================