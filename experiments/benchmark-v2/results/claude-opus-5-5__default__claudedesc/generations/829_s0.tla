---------------------------- MODULE CatInBoxes ----------------------------
EXTENDS Naturals

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 2

VARIABLES cat_box, observed_box, direction

vars == <<cat_box, observed_box, direction>>

Boxes == 1..Number_Of_Boxes

SearchBoxes == 2..(Number_Of_Boxes - 1)

Directions == {"left", "right"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in SearchBoxes
    /\ direction \in Directions

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = 2
    /\ direction = "right"

CatMove ==
    cat_box' \in ({cat_box - 1, cat_box + 1} \cap Boxes)

ObserverMove ==
    \/ /\ direction = "right"
       /\ IF observed_box + 1 \in SearchBoxes
             THEN /\ observed_box' = observed_box + 1
                  /\ direction' = direction
             ELSE /\ observed_box' = observed_box
                  /\ direction' = "left"
    \/ /\ direction = "left"
       /\ IF observed_box - 1 \in SearchBoxes
             THEN /\ observed_box' = observed_box - 1
                  /\ direction' = direction
             ELSE /\ observed_box' = observed_box
                  /\ direction' = "right"

Next ==
    /\ CatMove
    /\ ObserverMove

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CatMove)

Victory == <>(observed_box = cat_box)

THEOREM Spec => []TypeOK
THEOREM Spec => Victory
=============================================================================