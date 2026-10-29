------------------------- MODULE APADiningPhilosophers -------------------------
(***************************************************************************)
(* Apalache-oriented wrapper around the DiningPhilosophers specification.  *)
(* It declares the constants and variables with Apalache type annotations  *)
(* and instantiates the underlying module. The original specification      *)
(* stays free of tool-specific details. Init, Next, Spec and all           *)
(* invariants and properties come from the unnamed INSTANCE below.         *)
(***************************************************************************)

CONSTANTS
    \* @type: Int;
    NP

VARIABLES
    \* @type: Int -> {holder: Int, clean: Bool};
    forks,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    hungry

INSTANCE DiningPhilosophers

=============================================================================