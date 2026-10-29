---------------------------- MODULE MC_AsynchInterface ----------------------------
(***************************************************************************)
(* Apalache typing interface for the AsynchInterface specification.        *)
(*                                                                         *)
(* Apalache needs type annotations on every CONSTANT and VARIABLE. This    *)
(* module supplies those annotations and then instantiates the original    *)
(* AsynchInterface module, so the original spec stays free of              *)
(* tool-specific annotations.                                              *)
(*                                                                         *)
(* This module defines no transition actions, temporal formula or fault    *)
(* model of its own. Init, Next, Spec and the invariant are taken directly *)
(* from the instantiated module. The only design choice made here is a     *)
(* concrete enumerated value for the constant Data, used by the external   *)
(* model configuration.                                                    *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Set(Int);
    Data

VARIABLES
    \* @type: Int;
    val,
    \* @type: Int;
    rdy,
    \* @type: Int;
    ack

vars == <<val, rdy, ack>>

(***************************************************************************)
(* Constant initializer for Apalache (referenced via --cinit=ConstInit).   *)
(* It gives Data a concrete enumerated value.                              *)
(***************************************************************************)
ConstInit == Data = {0, 1, 2}

(***************************************************************************)
(* Instantiate the untyped original specification.                         *)
(* Data, val, rdy and ack are substituted implicitly by name.              *)
(***************************************************************************)
AI == INSTANCE AsynchInterface

(***************************************************************************)
(* Re-export the definitions of the original specification.                *)
(* No new behavior is introduced.                                          *)
(***************************************************************************)
Init == AI!Init

Next == AI!Next

Spec == AI!Spec

(***************************************************************************)
(* Safety invariant inherited from AsynchInterface.                        *)
(***************************************************************************)
TypeInvariant == AI!TypeInvariant

=============================================================================