------------------------- MODULE APADiningPhilosophers -------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Dining Philosophers specification.    *)
(* Supplies type annotations for the constants and variables, then         *)
(* instantiates the underlying DiningPhilosophers module. The original     *)
(* module stays free of tool-specific details. Through the INSTANCE,       *)
(* Init, Next, Spec, the invariants and the liveness properties of         *)
(* DiningPhilosophers become available in this module.                     *)
(***************************************************************************)

CONSTANTS
    \* Number of philosophers
    \* @type: Int;
    NP

VARIABLES
    \* Each fork records which philosopher holds it and whether it is clean
    \* @type: Int -> [holder: Int, clean: Bool];
    forks,
    \* Program counter of each philosopher process
    \* @type: Int -> Str;
    pc,
    \* Whether each philosopher is hungry
    \* @type: Int -> Bool;
    hungry

INSTANCE DiningPhilosophers

=============================================================================