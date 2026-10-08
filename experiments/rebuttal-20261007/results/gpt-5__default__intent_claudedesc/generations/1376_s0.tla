----------------------------- MODULE GrowingSet -----------------------------

EXTENDS Naturals

CONSTANTS Data

VARIABLES S

(*
  A simple monotonically growing set over a small, concrete universe.
  The universe is fixed here to two elements {0, 1}.
*)
ASSUME Data = {0, 1}

Init ==
  S = {}

Next ==
  \E x \in Data \ S :
    S' = S \cup {x}

Spec ==
  Init /\ [][Next]_S

=============================================================================