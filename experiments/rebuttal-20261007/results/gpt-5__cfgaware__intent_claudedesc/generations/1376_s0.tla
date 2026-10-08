----------------------------- MODULE GrowingSet -----------------------------

EXTENDS Naturals

(*
A simple monotonically growing set over a fixed, finite universe of data.
The universe is concrete and small: two elements {0, 1}.
*)

CONSTANTS

VARIABLES S

Data == {0, 1}

Init == S = {}

Next ==
  ∃ x \in (Data \ S) : S' = S \cup {x}

Spec == Init /\ [][Next]_S

============================================================================