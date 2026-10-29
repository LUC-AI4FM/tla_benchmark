---------------------------- MODULE CatInBoxes ----------------------------
(***************************************************************************)
(* A cat hides in one of N boxes arranged in a line. Each round the cat    *)
(* must move to an adjacent box. She cannot stay put and cannot wrap       *)
(* around. Each round the searcher inspects exactly one box. The searcher  *)
(* sweeps back and forth through the interior boxes 2..N-1, repeating the  *)
(* endpoint when reversing direction. For N = 5 this gives                 *)
(* 2,3,4,4,3,2,2,3,4,...                                                   *)
(* The cat's move and the searcher's next inspection happen at the same    *)
(* time.                                                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

VARIABLES cat, guess, dir

vars == <<cat, guess, dir>>

Boxes == 1..N

\* The interior sweep range. For N = 2 there are no interior boxes, so the
\* searcher always inspects box 1 (the sweep degenerates to a single box).
Lo == IF N > 2 THEN 2 ELSE 1
Hi == IF N > 2 THEN N - 1 ELSE 1

SearchRange == Lo..Hi

Directions == {"up", "down"}

\* Adjacent boxes the cat may move to (no staying, no wrap-around).
Neighbors(b) == {x \in Boxes : x = b - 1 \/ x = b + 1}

TypeOK ==
    /\ cat \in Boxes
    /\ guess \in SearchRange
    /\ dir \in Directions

Captured == cat = guess

\* The cat starts anywhere. The searcher may start at any point of the sweep,
\* going in either direction.
Init ==
    /\ cat \in Boxes
    /\ guess \in SearchRange
    /\ dir \in Directions

\* Deterministic sweep. When the searcher reaches an end of the range, it
\* inspects that end once more and then reverses direction.
SearcherMove ==
    IF dir = "up"
    THEN IF guess = Hi
         THEN /\ guess' = guess
              /\ dir' = "down"
         ELSE /\ guess' = guess + 1
              /\ dir' = dir
    ELSE IF guess = Lo
         THEN /\ guess' = guess
              /\ dir' = "up"
         ELSE /\ guess' = guess - 1
              /\ dir' = dir

\* The cat moves adversarially to any adjacent box.
CatMove ==
    cat' \in Neighbors(cat)

\* A round happens simultaneously, and only while the cat is still uncaught.
Round ==
    /\ ~Captured
    /\ CatMove
    /\ SearcherMove

Next == Round

\* Weak fairness: the cat keeps moving and cannot stall forever.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
(* Safety properties *)

TypeInvariant == TypeOK

\* The cat always occupies a valid box.
CatInBounds == cat \in Boxes

\* The searcher always inspects a box within the sweep range.
GuessInRange == guess \in SearchRange

\* After the cat is captured, nothing changes.
CaptureIsFinal == [][Captured => UNCHANGED vars]_vars

(* Liveness property *)

\* Guaranteed capture: for every starting box and every adversarial choice
\* of moves, the searcher eventually inspects the cat's box.
GuaranteedCapture == <>Captured

\* Once caught, the cat stays caught.
StaysCaptured == [](Captured => []Captured)

THEOREM Spec => []TypeOK
THEOREM Spec => GuaranteedCapture
=============================================================================