---------------------------- MODULE CatInTheBox ----------------------------
(***************************************************************************)
(* The moving-cat puzzle.  N boxes are arranged in a line, numbered 1..N.  *)
(* A cat hides in one box.  Every step the cat must move to an adjacent    *)
(* box, with no wrap-around.  On each step the observer opens one box.     *)
(* The observer sweeps boxes 2 .. N-1 back and forth.  At each end it      *)
(* checks the end box a second time while reversing direction:             *)
(*     2, 3, ..., N-1, N-1, N-2, ..., 2, 2, 3, ...                         *)
(* This pattern is guaranteed to find the cat.                             *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 3

VARIABLES
    cat,        \* the box the cat is currently in
    observed,   \* the box the observer currently checks
    direction   \* the current sweep direction of the observer: 1 or -1

vars == << cat, observed, direction >>

Boxes       == 1 .. N
SearchBoxes == 2 .. (N - 1)

TypeOK ==
    /\ cat \in Boxes
    /\ observed \in SearchBoxes
    /\ direction \in {-1, 1}

-----------------------------------------------------------------------------

Init ==
    /\ cat \in Boxes
    /\ observed = 2
    /\ direction = 1

(* The cat must move to an adjacent box. It cannot wrap around. *)
CatMove ==
    /\ cat' \in {cat - 1, cat + 1} \cap Boxes

(* The observer follows the back-and-forth search pattern over 2..N-1.  *)
(* At an end, it reverses direction and checks the same box again.      *)
Observe ==
    IF direction = 1
    THEN IF observed = N - 1
         THEN /\ direction' = -1
              /\ observed' = observed
         ELSE /\ direction' = direction
              /\ observed' = observed + 1
    ELSE IF observed = 2
         THEN /\ direction' = 1
              /\ observed' = observed
         ELSE /\ direction' = direction
              /\ observed' = observed - 1

(* Each step, the cat moves and the observer moves to its next box. *)
Next ==
    /\ CatMove
    /\ Observe

Spec == Init /\ [][Next]_vars /\ WF_vars(CatMove)

-----------------------------------------------------------------------------

(* Safety: the variables always stay well typed. *)
THEOREM Spec => []TypeOK

(* Liveness: the observer eventually opens the box the cat is in. *)
Victory == <>(observed = cat)

THEOREM Spec => Victory

=============================================================================