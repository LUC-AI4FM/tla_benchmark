---------------------------- MODULE CatInBoxes ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 3

Boxes == 1..N

VARIABLES cat, observed, direction

vars == <<cat, observed, direction>>

TypeOK ==
    /\ cat \in Boxes
    /\ observed \in 2..(N-1)
    /\ direction \in {"up", "down"}

-----------------------------------------------------------------------------
Init ==
    /\ cat \in Boxes
    /\ observed = 2
    /\ direction = "up"

\* The cat must move to an adjacent box (no wrap-around).
CatMove ==
    \/ /\ cat > 1
       /\ cat' = cat - 1
    \/ /\ cat < N
       /\ cat' = cat + 1

\* The observer sweeps back and forth over boxes 2..N-1.
\* At each end it checks the end box once more and reverses direction.
Observe ==
    IF direction = "up"
    THEN IF observed < N - 1
         THEN /\ observed' = observed + 1
              /\ UNCHANGED direction
         ELSE /\ observed' = observed
              /\ direction' = "down"
    ELSE IF observed > 2
         THEN /\ observed' = observed - 1
              /\ UNCHANGED direction
         ELSE /\ observed' = observed
              /\ direction' = "up"

Next ==
    /\ CatMove
    /\ Observe

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ WF_<<cat>>(CatMove)

-----------------------------------------------------------------------------
\* Properties

Victory == <>(observed = cat)

THEOREM Spec => []TypeOK
THEOREM Spec => Victory
=============================================================================