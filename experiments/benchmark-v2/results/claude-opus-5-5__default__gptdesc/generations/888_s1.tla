------------------------- MODULE MC_AsynchInterface -------------------------
(***************************************************************************)
(* Apalache typing interface for the AsynchInterface specification.        *)
(*                                                                         *)
(* This module declares typed versions of the constant and variables of    *)
(* AsynchInterface and then instantiates that module, so the original      *)
(* specification can stay free of tool-specific type annotations.          *)
(*                                                                         *)
(* No transition actions, temporal specification or fault model are        *)
(* defined here. Init, Next, Spec and TypeInvariant all come from the      *)
(* instantiated AsynchInterface module.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLES
    \* @type: Int;
    val,
    \* @type: Int;
    rdy,
    \* @type: Int;
    ack

(***************************************************************************)
(* A concrete enumerated value for the Data constant. External model       *)
(* configuration uses it, either through a TLC substitution                *)
(* (Data <- MCData) or through Apalache's constant initializer             *)
(* (--cinit=ConstInit).                                                    *)
(***************************************************************************)
MCData == {0, 1, 2}

ConstInit == Data = MCData

(***************************************************************************)
(* Instantiate the underlying specification. The constant and variables    *)
(* declared above replace the identically named parameters of              *)
(* AsynchInterface. This brings its Init, Next, Spec and TypeInvariant     *)
(* into scope.                                                             *)
(***************************************************************************)
INSTANCE AsynchInterface

=============================================================================