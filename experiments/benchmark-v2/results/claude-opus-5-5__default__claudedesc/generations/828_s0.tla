---------------------------- MODULE ApaCat ----------------------------
(***************************************************************************)
(* Type-annotated wrapper of the "Cat" specification for Apalache.        *)
(* A cat moves among a row of boxes. Each night it jumps to an adjacent   *)
(* box. Each morning an observer opens one box. The observer sweeps       *)
(* across the boxes, and the sweep direction is recorded in `direction`.  *)
(* The definitions of the Cat module are included inline so that this     *)
(* module is self-contained and passes SANY.                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

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

\* Constant initialization for Apalache (Number_Of_Boxes = 4 in the config)
CInit == Number_Of_Boxes = 4

ASSUME NumberAssumption == Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 1

Boxes == 1..Number_Of_Boxes

Directions == {"left", "right"}

\* Bounds of the observer's sweep: boxes 2 .. N-1 (or box 1 for small N)
Lo == IF Number_Of_Boxes > 2 THEN 2 ELSE 1
Hi == IF Number_Of_Boxes > 2 THEN Number_Of_Boxes - 1 ELSE 1

-----------------------------------------------------------------------------
TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in Boxes
    /\ direction \in Directions

CatFound == cat_box = observed_box

-----------------------------------------------------------------------------
Init ==
    /\ cat_box \in Boxes
    /\ observed_box = Lo
    /\ direction = "right"

\* Each night the cat moves to an adjacent box
CatMove ==
    /\ cat_box' \in ({cat_box - 1, cat_box + 1} \cap Boxes)

\* The observer sweeps right to Hi, then left back to Lo, and so on.
\* At each end the end box is checked twice (direction reverses).
ObserverMove ==
    IF direction = "right"
    THEN IF observed_box < Hi
         THEN /\ observed_box' = observed_box + 1
              /\ direction' = "right"
         ELSE /\ observed_box' = observed_box
              /\ direction' = "left"
    ELSE IF observed_box > Lo
         THEN /\ observed_box' = observed_box - 1
              /\ direction' = "left"
         ELSE /\ observed_box' = observed_box
              /\ direction' = "right"

\* One day passes: cat was not found, the cat moves and the observer
\* chooses the next box to check.
Step ==
    /\ ~CatFound
    /\ CatMove
    /\ ObserverMove

\* Once the cat is found the system stays in that state
Done ==
    /\ CatFound
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety: the type invariant
THEOREM Spec => []TypeOK

\* Liveness: the observer eventually finds the cat
CatEventuallyFound == <>CatFound

THEOREM Spec => CatEventuallyFound
=============================================================================