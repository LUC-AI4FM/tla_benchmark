---------------------------- MODULE APDiningPhilosophers ----------------------------
(***************************************************************************)
(* Apalache-oriented wrapper around the DiningPhilosophers specification.  *)
(* It only supplies type annotations for the constants and variables and  *)
(* then instantiates the underlying DiningPhilosophers module. This keeps  *)
(* the original specification free of tool-specific details.              *)
(*                                                                         *)
(* Init, Next, Spec and all invariants and properties come from the        *)
(* instantiated DiningPhilosophers module.                                 *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* Number of philosophers
    \* @type: Int;
    NP

VARIABLES
    \* Each fork has a holder (a philosopher id) and a cleanliness flag
    \* @type: Int -> { holder: Int, clean: Bool };
    forks,
    \* PlusCal program counter for each philosopher process
    \* @type: Int -> Str;
    pc,
    \* Per-philosopher local flag: is the philosopher hungry?
    \* @type: Int -> Bool;
    hungry

INSTANCE DiningPhilosophers

=============================================================================