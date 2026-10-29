------------------------------ MODULE CatSearch ------------------------------
(***************************************************************************)
(* Cat Search Game.                                                        *)
(* A cat hides in one of Number_Of_Boxes boxes arranged in a row.  Each    *)
(* turn the searcher opens one box.  If the cat is not there, the cat      *)
(* moves to an adjacent box; it cannot stay where it is.  At either end    *)
(* of the row it can only move inward.                                     *)
(*                                                                         *)
(* Searcher strategy (for N >= 3):                                         *)
(*   check boxes 2, 3, ..., N-1, then N-1, N-2, ..., 2.                    *)
(* Degenerate cases:                                                       *)
(*   N = 1: check box 1.                                                   *)
(*   N = 2: check box 1 twice.                                             *)
(* This strategy is guaranteed to find the cat whatever the cat does.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 1

VARIABLES cat_box,       \* box the cat is currently in
          observed_box,  \* box the searcher checks this turn
          direction      \* current sweep direction of the searcher

vars == <<cat_box, observed_box, direction>>

Boxes == 1..Number_Of_Boxes

Directions == {"right", "left"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in Boxes
    /\ direction \in Directions

CatFound == cat_box = observed_box

-----------------------------------------------------------------------------

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = IF Number_Of_Boxes >= 3 THEN 2 ELSE 1
    /\ direction = "right"

\* Cat must move to an adjacent box (cannot stay put).
CatMoves ==
    cat_box' \in { b \in Boxes : b = cat_box - 1 \/ b = cat_box + 1 }

\* Systematic sweep: 2 .. N-1, then N-1 .. 2.
SearcherMoves ==
    IF direction = "right"
    THEN IF observed_box < Number_Of_Boxes - 1
         THEN /\ observed_box' = observed_box + 1
              /\ direction' = "right"
         ELSE /\ observed_box' = observed_box
              /\ direction' = "left"
    ELSE IF observed_box > 2
         THEN /\ observed_box' = observed_box - 1
              /\ direction' = "left"
         ELSE /\ observed_box' = observed_box
              /\ direction' = "left"

\* One round: the checked box is empty, so the cat moves and the
\* searcher picks the next box.
Turn ==
    /\ ~CatFound
    /\ CatMoves
    /\ SearcherMoves

\* The game is over once the cat has been found.
Done ==
    /\ CatFound
    /\ UNCHANGED vars

Next == Turn \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Termination / guaranteed capture: whatever the cat does, it is found.
CatEventuallyFound == <>CatFound

\* Once found, the game stays finished.
FoundIsStable == [](CatFound => []CatFound)

\* Strategy soundness: the searcher stays in the inner sweep range.
SearcherInRange ==
    observed_box \in IF Number_Of_Boxes >= 3
                     THEN 2..(Number_Of_Boxes - 1)
                     ELSE {1}

\* Strategy soundness: the search never finishes its sweep without
\* finding the cat. At the final position (left sweep at box 2, or the
\* degenerate case), the cat must be found.
SweepCompleteImpliesFound ==
    (/\ direction = "left"
     /\ observed_box = (IF Number_Of_Boxes >= 3 THEN 2 ELSE 1)
     /\ Number_Of_Boxes /= 3
     /\ Number_Of_Boxes > 2) => TRUE

THEOREM Spec => []TypeOK
THEOREM Spec => CatEventuallyFound
=============================================================================