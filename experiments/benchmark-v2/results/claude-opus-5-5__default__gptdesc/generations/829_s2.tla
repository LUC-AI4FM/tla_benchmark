---------------------------- MODULE CatInBoxes ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 3

Boxes == 1..N

VARIABLES cat_box, observed_box, direction

vars == <<cat_box, observed_box, direction>>

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in 2..(N - 1)
    /\ direction \in {"up", "down"}

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = 2
    /\ direction = "up"

\* The cat must move to an adjacent box every step, with no wrap-around.
MoveCat ==
    \/ /\ cat_box > 1
       /\ cat_box' = cat_box - 1
    \/ /\ cat_box < N
       /\ cat_box' = cat_box + 1

\* The observer sweeps back and forth over boxes 2..N-1, checking each
\* end box twice when reversing direction (2,3,...,N-1,N-1,...,3,2,2,...).
Observe ==
    IF direction = "up"
    THEN IF observed_box = N - 1
         THEN /\ direction' = "down"
              /\ observed_box' = N - 1
         ELSE /\ direction' = "up"
              /\ observed_box' = observed_box + 1
    ELSE IF observed_box = 2
         THEN /\ direction' = "up"
              /\ observed_box' = 2
         ELSE /\ direction' = "down"
              /\ observed_box' = observed_box - 1

Next == MoveCat /\ Observe

Spec == Init /\ [][Next]_vars /\ WF_vars(MoveCat)

CatFound == observed_box = cat_box

Victory == <>CatFound

THEOREM Spec => []TypeOK
THEOREM Spec => Victory
=============================================================================