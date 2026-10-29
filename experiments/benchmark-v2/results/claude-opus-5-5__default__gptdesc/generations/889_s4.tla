---------------------------- MODULE ApaChannel ----------------------------
(***************************************************************************)
(* A thin wrapper around the Channel specification that adds Apalache     *)
(* type annotations, leaving the original Channel module unchanged.        *)
(* Init, Next, Spec, TypeInvariant and the channel actions all come from   *)
(* INSTANCE Channel. They are deliberately not redefined here.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: [val: Int, rdy: Int, ack: Int];
    chan

(***************************************************************************)
(* A concrete set of data values. It can be used to instantiate the        *)
(* constant Data, for example with a ConstInit or a model override.        *)
(***************************************************************************)
\* @type: Set(Int);
DataVal == 0..2

INSTANCE Channel
=============================================================================