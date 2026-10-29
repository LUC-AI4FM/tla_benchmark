---------------------------- MODULE CatInTheBox ----------------------------
EXTENDS Integers

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 2

VARIABLES cat_box, observed_box, direction

vars == <<cat_box, observed_box, direction>>

Boxes == 1..Number_Of_Boxes

ObservableBoxes == 2..(Number_Of_Boxes - 1)

Directions == {"left", "right"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in ObservableBoxes
    /\ direction \in Directions

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = 2
    /\ direction = "right"

CatMove ==
    \E d \in {-1, 1} :
        /\ cat_box + d \in Boxes
        /\ cat_box' = cat_box + d

ObserverMove ==
    IF direction = "right"
    THEN IF observed_box + 1 \in ObservableBoxes
         THEN /\ observed_box' = observed_box + 1
              /\ direction' = direction
         ELSE /\ direction' = "left"
              /\ observed_box' = observed_box
    ELSE IF observed_box - 1 \in ObservableBoxes
         THEN /\ observed_box' = observed_box - 1
              /\ direction' = direction
         ELSE /\ direction' = "right"
              /\ observed_box' = observed_box

Next == CatMove /\ ObserverMove

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Victory == <>(observed_box = cat_box)

=============================================================================