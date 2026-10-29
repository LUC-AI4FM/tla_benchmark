------------------------------ MODULE CatInBoxes ------------------------------
EXTENDS Naturals

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 2

VARIABLES cat_box, search_box, direction

vars == <<cat_box, search_box, direction>>

Boxes == 1..Number_Of_Boxes

\* Interior sweep range (excluding the endpoints). For N = 2 the range
\* degenerates to the single box 2.
Low  == 2
High == IF Number_Of_Boxes - 1 >= 2 THEN Number_Of_Boxes - 1 ELSE 2

SweepRange == Low..High

Directions == {"up", "down"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ search_box \in Boxes
    /\ direction \in Directions

Init ==
    /\ cat_box \in Boxes
    /\ search_box \in SweepRange
    /\ direction \in Directions

\* The cat must move to an adjacent box. No staying, no wrap-around.
CatMoves ==
    \/ /\ cat_box > 1
       /\ cat_box' = cat_box - 1
    \/ /\ cat_box < Number_Of_Boxes
       /\ cat_box' = cat_box + 1

\* The searcher sweeps back and forth through the interior range.
\* At either end of the range, the same box is inspected again and
\* the direction is reversed (e.g. 2,3,4,4,3,2,2,3,4,...).
SearcherMoves ==
    IF direction = "up"
    THEN IF search_box >= High
         THEN /\ search_box' = search_box
              /\ direction' = "down"
         ELSE /\ search_box' = search_box + 1
              /\ direction' = "up"
    ELSE IF search_box <= Low
         THEN /\ search_box' = search_box
              /\ direction' = "up"
         ELSE /\ search_box' = search_box - 1
              /\ direction' = "down"

\* Cat movement and searcher observation happen simultaneously.
Next ==
    /\ CatMoves
    /\ SearcherMoves

\* The cat must keep moving (she cannot stop indefinitely).
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Guaranteed capture: eventually the searcher inspects the cat's box.
Victory == <>(cat_box = search_box)

=============================================================================