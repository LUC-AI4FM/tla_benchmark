---------------------------- MODULE Apa_Cat ----------------------------
(***************************************************************************)
(* Type-annotated specification of the "Cat" puzzle, for use with the     *)
(* Apalache model checker. A cat hides in one of Number_Of_Boxes boxes    *)
(* arranged in a row. Each step the cat moves to an adjacent box. An      *)
(* observer opens one box per step, sweeping in a given direction, and    *)
(* tries to find the cat.                                                  *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    Number_Of_Boxes

VARIABLES
    \* @type: Int;
    cat_box,
    \* @type: Int;
    observed_box,
    \* @type: Str;
    direction

vars == <<cat_box, observed_box, direction>>

Boxes == 1..Number_Of_Boxes

Directions == {"left", "right"}

\* Lowest and highest boxes the observer sweeps over (the classic strategy
\* checks boxes 2 .. N-1 and back again).
LowSweep  == IF Number_Of_Boxes >= 3 THEN 2 ELSE 1
HighSweep == IF Number_Of_Boxes >= 3 THEN Number_Of_Boxes - 1 ELSE Number_Of_Boxes

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in Boxes
    /\ direction \in Directions

CatFound == cat_box = observed_box

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = LowSweep
    /\ direction = "right"

\* The cat moves to a neighbouring box.
CatMoves ==
    cat_box' \in { b \in Boxes : b = cat_box - 1 \/ b = cat_box + 1 }

\* The observer advances its sweep.
ObserverMoves ==
    IF direction = "right"
    THEN IF observed_box < HighSweep
         THEN /\ observed_box' = observed_box + 1
              /\ direction' = direction
         ELSE /\ observed_box' = observed_box
              /\ direction' = "left"
    ELSE IF observed_box > LowSweep
         THEN /\ observed_box' = observed_box - 1
              /\ direction' = direction
         ELSE /\ observed_box' = observed_box
              /\ direction' = "right"

Step ==
    /\ ~CatFound
    /\ CatMoves
    /\ ObserverMoves

\* Once the cat has been found, the system stays put.
Done ==
    /\ CatFound
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

=============================================================================