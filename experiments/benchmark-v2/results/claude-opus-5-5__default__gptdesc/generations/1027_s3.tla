--------------------------- MODULE APAChangRoberts ---------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Chang-Roberts leader election spec.  *)
(* This module only supplies type annotations for the constants and       *)
(* variables, together with concrete values for the constants (NVal and   *)
(* IdVal). The behavior comes from the original ChangRoberts module via   *)
(* INSTANCE. That includes Init, Next, Spec, the fairness conditions, the  *)
(* safety invariants and the liveness properties. None of these are       *)
(* redefined here, so the original specification stays separate and       *)
(* tool-agnostic.                                                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Seq(Int);
    Id

VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

(***************************************************************************)
(* Concrete values for the constants, used by Apalache, e.g.               *)
(*   apalache-mc check --cinit=... or via N <- NVal, Id <- IdVal.         *)
(***************************************************************************)
NVal == 3

IdVal == <<3, 1, 2>>

(***************************************************************************)
(* Import the main behavior from the original ChangRoberts specification. *)
(* This brings Node, Init, Next, Spec, the fairness conditions, the       *)
(* type invariants, the safety properties and the liveness properties     *)
(* into scope unqualified. The constants and variables declared above are *)
(* substituted implicitly by name.                                        *)
(***************************************************************************)
INSTANCE ChangRoberts

=============================================================================