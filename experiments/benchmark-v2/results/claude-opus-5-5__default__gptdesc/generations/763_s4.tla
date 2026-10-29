------------------------- MODULE APADiningPhilosophers -------------------------
(***************************************************************************)
(* Apalache wrapper for the DiningPhilosophers specification.              *)
(*                                                                         *)
(* This module only supplies Apalache type annotations for the constants   *)
(* and variables of the DiningPhilosophers model. The original             *)
(* specification stays free of tool-specific details.                      *)
(*                                                                         *)
(* All definitions come from the unnamed INSTANCE below. These include     *)
(* Init, Next, Spec, the type and safety invariants, the liveness          *)
(* properties and the fairness conditions. They are therefore available   *)
(* in this module under their original names.                              *)
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
    \* Whether each philosopher is currently hungry
    \* @type: Int -> Bool;
    hungry

INSTANCE DiningPhilosophers

================================================================================