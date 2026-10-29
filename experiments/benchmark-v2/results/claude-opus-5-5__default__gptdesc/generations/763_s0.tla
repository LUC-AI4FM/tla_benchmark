------------------------- MODULE APADiningPhilosophers -------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Dining Philosophers specification.   *)
(* It supplies type annotations for the constants and variables of the     *)
(* underlying DiningPhilosophers module, then instantiates that module.    *)
(* The original specification stays free of tool-specific details.         *)
(*                                                                         *)
(* Init, Next, Spec and the invariants and properties are not defined      *)
(* here. They come from the instantiated DiningPhilosophers module.        *)
(***************************************************************************)

CONSTANTS
    \* @type: Int;
    NP

VARIABLES
    \* @type: Int -> [holder: Int, clean: Bool];
    forks,
    \* @type: Int -> Bool;
    hungry,
    \* @type: Int -> Str;
    pc

INSTANCE DiningPhilosophers

================================================================================