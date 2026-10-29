-------------------------- MODULE APChangRoberts --------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Chang-Roberts leader election         *)
(* specification. This module only supplies type annotations for the      *)
(* constants and variables, plus concrete values for the constants.        *)
(*                                                                         *)
(* The behavior (Init, Next, Spec), the invariants and the liveness        *)
(* properties all come from the instantiated module ChangRoberts. This     *)
(* module adds no transition relation, temporal formula, fairness          *)
(* condition or proof of its own, so the original specification stays     *)
(* separate from the tool-specific material.                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* Number of nodes in the ring.
    \* @type: Int;
    N,
    \* Sequence of distinct node identifiers, indexed by node.
    \* @type: Seq(Int);
    Id

VARIABLES
    \* Messages in transit, one set per node.
    \* @type: Int -> Set(Int);
    msgs,
    \* Program counter of each process.
    \* @type: Int -> Str;
    pc,
    \* Whether each node initiates the election.
    \* @type: Int -> Bool;
    initiator,
    \* Local state of each node: "cand", "lost" or "won".
    \* @type: Int -> Str;
    state

(***************************************************************************)
(* Concrete values for the constants. Apalache uses these through a        *)
(* ConstInit or a configuration that substitutes N <- NVal, Id <- IdVal.   *)
(***************************************************************************)
\* @type: Int;
NVal == 3

\* @type: Seq(Int);
IdVal == <<3, 1, 2>>

\* Optional constant initializer for Apalache's --cinit option.
ConstInit ==
    /\ N = NVal
    /\ Id = IdVal

(***************************************************************************)
(* Import the main behavior from the original specification. This brings   *)
(* in Init, Next, Spec and the safety and liveness properties defined      *)
(* there. Constants and variables with the same names are substituted      *)
(* implicitly.                                                             *)
(***************************************************************************)
INSTANCE ChangRoberts

=============================================================================