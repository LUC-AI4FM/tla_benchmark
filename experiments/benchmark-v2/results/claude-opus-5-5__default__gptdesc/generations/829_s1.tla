---------------------------- MODULE CatInABox ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 3

VARIABLES cat_box, observed_box, direction

vars == <<cat_box, observed_box, direction>>

Boxes == 1..N

SearchBoxes == 2..(N - 1)

Directions == {"right", "left"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in SearchBoxes
    /\ direction \in Directions

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = 2
    /\ direction = "right"

\* The cat moves to an adjacent box, with no wrap-around.
MoveCat ==
    cat_box' \in { b \in Boxes : b = cat_box - 1 \/ b = cat_box + 1 }

\* The observer follows a back-and-forth pattern over boxes 2..N-1.
\* At each end it reverses direction and checks that end box again.
Observe ==
    IF direction = "right"
    THEN IF observed_box >= N - 1
         THEN /\ direction' = "left"
              /\ observed_box' = N - 1
         ELSE /\ direction' = "right"
              /\ observed_box' = observed_box + 1
    ELSE IF observed_box <= 2
         THEN /\ direction' = "right"
              /\ observed_box' = 2
         ELSE /\ direction' = "left"
              /\ observed_box' = observed_box - 1

\* Each step, the cat moves and the observer checks the next box in the pattern.
Next ==
    /\ MoveCat
    /\ Observe

\* Weak fairness on the step that moves the cat.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

CatFound == observed_box = cat_box

\* The observed box eventually coincides with the cat's box.
Victory == <>CatFound

THEOREM Spec => []TypeOK
THEOREM Spec => Victory
=============================================================================