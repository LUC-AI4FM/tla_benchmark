---------------------------- MODULE MC_AsynchInterface ----------------------------
(***************************************************************************)
(* A lightweight Apalache typing interface for the AsynchInterface spec.   *)
(* It declares typed versions of the constant and variables of             *)
(* AsynchInterface and instantiates it, so that the original specification *)
(* remains free of tool-specific type annotations.                         *)
(***************************************************************************)
EXTENDS Naturals

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

\* A concrete enumerated value for the data constant, referenced from the
\* external model configuration (e.g., ConstInit / CONSTANT Data <- ConstData).
ConstData == {0, 1, 2}

\* Apalache-style constant initializer
ConstInit == Data = ConstData

\* Instantiate the underlying, annotation-free specification
AI == INSTANCE AsynchInterface WITH Data <- Data, val <- val, rdy <- rdy, ack <- ack

vars == <<val, rdy, ack>>

Init == AI!Init

Next == AI!Next

Spec == Init /\ [][Next]_vars

TypeInvariant == AI!TypeInvariant

=============================================================================