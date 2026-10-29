------------------------------ MODULE CatInBoxes ------------------------------
EXTENDS Integers

CONSTANT Number_Of_Boxes

ASSUME NBoxesAssumption ==
    /\ Number_Of_Boxes \in Nat
    /\ Number_Of_Boxes >= 2

VARIABLES cat_box, search_box, direction

vars == << cat_box, search_box, direction >>

Boxes == 1 .. Number_Of_Boxes

\* The sweep covers only the interior boxes 2 .. N-1. When N = 2 there is
\* no interior, so the sweep degenerates to inspecting box 1 every step.
\* That still guarantees discovery for N = 2.
SweepLo == IF Number_Of_Boxes > 2 THEN 2 ELSE 1
SweepHi == IF Number_Of_Boxes > 2 THEN Number_Of_Boxes - 1 ELSE 1

Interior == SweepLo .. SweepHi

Directions == {1, -1}

\* The adversary must move to an adjacent box. It cannot stay still or wrap around.
CatMoves(c) == { c - 1, c + 1 } \cap Boxes

\* The deterministic sweep strategy. At an interior endpoint the searcher
\* inspects the same box once more and reverses direction. This gives the
\* periodic sequence 2,3,...,N-1,N-1,N-2,...,2,2,3,...
NextSearchBox(p, d) ==
    IF d = 1
        THEN IF p = SweepHi THEN p ELSE p + 1
        ELSE IF p = SweepLo THEN p ELSE p - 1

NextDirection(p, d) ==
    IF d = 1
        THEN IF p = SweepHi THEN -1 ELSE 1
        ELSE IF p = SweepLo THEN 1 ELSE -1

TypeOK ==
    /\ cat_box \in Boxes
    /\ search_box \in Interior
    /\ direction \in Directions

\* Any initial cat position and any phase of the sweep.
Init ==
    /\ cat_box \in Boxes
    /\ search_box \in Interior
    /\ direction \in Directions

\* Adversary transition: a nondeterministic move to an adjacent box.
CatMove ==
    cat_box' \in CatMoves(cat_box)

\* Searcher transition: a deterministic step of the sweep, reversing at the interior ends.
SearcherMove ==
    /\ search_box' = NextSearchBox(search_box, direction)
    /\ direction'  = NextDirection(search_box, direction)

\* One time step: the cat moves and the searcher chooses its next inspection.
Next ==
    /\ CatMove
    /\ SearcherMove

\* Fairness: time always advances, so the adversary moves every step.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* A time step where the inspected box holds the cat.
Found == cat_box = search_box

\* Eventual discovery. It holds for every N >= 2, both even and odd,
\* from any initial position and any phase of the sweep.
Victory == <>Found

BoundsInvariant ==
    /\ cat_box \in 1 .. Number_Of_Boxes
    /\ search_box \in SweepLo .. SweepHi

THEOREM Spec => []TypeOK
THEOREM Spec => []BoundsInvariant
THEOREM Spec => Victory
================================================================================