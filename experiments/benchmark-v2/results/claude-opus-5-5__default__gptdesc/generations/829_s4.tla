---------------------------- MODULE CatPuzzle ----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 3

VARIABLES cat, observed, direction

vars == <<cat, observed, direction>>

Boxes == 1..N

TypeOK ==
    /\ cat \in Boxes
    /\ observed \in 2..(N - 1)
    /\ direction \in {-1, 1}

Init ==
    /\ cat \in Boxes
    /\ observed = 2
    /\ direction = 1

(* The cat must move to an adjacent box, with no wrap-around. *)
CatMove ==
    cat' \in {c \in Boxes : c = cat - 1 \/ c = cat + 1}

(* The observer sweeps 2..N-1 back and forth. At each end it checks *)
(* the end box a second time and reverses direction.                *)
Observe ==
    IF direction = 1
    THEN IF observed = N - 1
         THEN /\ direction' = -1
              /\ observed' = observed
         ELSE /\ observed' = observed + 1
              /\ direction' = direction
    ELSE IF observed = 2
         THEN /\ direction' = 1
              /\ observed' = observed
         ELSE /\ observed' = observed - 1
              /\ direction' = direction

Next == CatMove /\ Observe

Spec == Init /\ [][Next]_vars /\ WF_vars(CatMove)

(* Safety *)
Inv == TypeOK

(* Liveness: the observer eventually finds the cat. *)
Victory == <>(observed = cat)

THEOREM Spec => []TypeOK
THEOREM Spec => Victory
=============================================================================