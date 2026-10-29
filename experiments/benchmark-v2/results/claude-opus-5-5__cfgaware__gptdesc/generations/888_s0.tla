---------------------------- MODULE ApaAsynchInterface ----------------------------
(***************************************************************************)
(* A typing interface for AsynchInterface, intended for use with Apalache. *)
(* It declares the constant and the variables with type annotations, then  *)
(* instantiates AsynchInterface, so the original specification needs no    *)
(* tool-specific annotations.                                              *)
(*                                                                         *)
(* The unnamed INSTANCE brings TypeInvariant, Spec and the other operators *)
(* of AsynchInterface into scope. DataVal gives a concrete enumerated      *)
(* value that a model configuration can substitute for Data, for example   *)
(* with: CONSTANT Data <- DataVal                                          *)
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

INSTANCE AsynchInterface

\* A concrete value for the data constant, used by external model configuration.
DataVal == {0, 1, 2}

=============================================================================