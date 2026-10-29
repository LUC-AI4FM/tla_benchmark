---------------------------- MODULE CatPuzzle ----------------------------
EXTENDS Naturals

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 3

VARIABLES cat_box, observed_box, direction

vars == <<cat_box, observed_box, direction>>

Boxes == 1..Number_Of_Boxes

SearchBoxes == 2..(Number_Of_Boxes - 1)

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in SearchBoxes
    /\ direction \in {"up", "down"}

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = 2
    /\ direction = "up"

\* The cat must move to an adjacent box (no wrap-around).
Move_Cat ==
    cat_box' \in ({cat_box - 1, cat_box + 1} \cap Boxes)

\* The observer sweeps back and forth over boxes 2 .. N-1,
\* checking the end box twice when reversing direction.
Observe ==
    \/ /\ direction = "up"
       /\ observed_box < Number_Of_Boxes - 1
       /\ observed_box' = observed_box + 1
       /\ direction' = "up"
    \/ /\ direction = "up"
       /\ observed_box = Number_Of_Boxes - 1
       /\ observed_box' = observed_box
       /\ direction' = "down"
    \/ /\ direction = "down"
       /\ observed_box > 2
       /\ observed_box' = observed_box - 1
       /\ direction' = "down"
    \/ /\ direction = "down"
       /\ observed_box = 2
       /\ observed_box' = observed_box
       /\ direction' = "up"

Next == Move_Cat /\ Observe

Spec == Init /\ [][Next]_vars /\ WF_vars(Move_Cat /\ Observe)

Victory == <>(observed_box = cat_box)

=============================================================================