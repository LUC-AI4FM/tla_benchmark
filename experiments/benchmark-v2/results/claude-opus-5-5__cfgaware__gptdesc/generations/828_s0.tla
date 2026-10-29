------------------------------- MODULE ApaCat -------------------------------
(***************************************************************************)
(* Wrapper around the Cat specification, with Apalache type annotations.  *)
(* The Cat behaviour is included inline so that the module is             *)
(* self-contained and parses on its own.                                  *)
(***************************************************************************)
EXTENDS Naturals

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

vars == << cat_box, observed_box, direction >>

Boxes == 1..Number_Of_Boxes

Directions == {"left", "right"}

TypeOK ==
    /\ cat_box \in Boxes
    /\ observed_box \in Boxes
    /\ direction \in Directions

\* Boxes the cat may move to from box b: an adjacent box (stays if alone).
CatMoves(b) ==
    IF Number_Of_Boxes = 1
    THEN {b}
    ELSE {c \in Boxes : c = b - 1 \/ c = b + 1}

Init ==
    /\ cat_box \in Boxes
    /\ observed_box = IF Number_Of_Boxes >= 3 THEN 2 ELSE 1
    /\ direction = "right"

\* The observer sweeps boxes 2..N-1 forwards and then backwards.
ObserverStep ==
    IF Number_Of_Boxes < 3
    THEN /\ observed_box' = observed_box
         /\ direction' = direction
    ELSE IF direction = "right"
         THEN IF observed_box < Number_Of_Boxes - 1
              THEN /\ observed_box' = observed_box + 1
                   /\ direction' = "right"
              ELSE /\ observed_box' = observed_box
                   /\ direction' = "left"
         ELSE IF observed_box > 2
              THEN /\ observed_box' = observed_box - 1
                   /\ direction' = "left"
              ELSE /\ observed_box' = observed_box
                   /\ direction' = "right"

Next ==
    /\ cat_box /= observed_box
    /\ cat_box' \in CatMoves(cat_box)
    /\ ObserverStep

Spec == Init /\ [][Next]_vars

=============================================================================