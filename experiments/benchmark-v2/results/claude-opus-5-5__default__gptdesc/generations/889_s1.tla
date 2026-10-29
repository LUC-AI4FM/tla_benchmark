---------------------------- MODULE ApaChannel ----------------------------
(***************************************************************************)
(* Thin wrapper around the Channel specification that adds Apalache type    *)
(* annotations while leaving the original Channel module unchanged.        *)
(* The channel behavior (TypeInvariant, Init, Send, Rcv, Next, Spec) is    *)
(* inherited from Channel via INSTANCE.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: { val: Int, rdy: Int, ack: Int };
    chan

\* Helper that names a data value with its Apalache type.
\* @type: Int => Int;
DataVal(d) == d

INSTANCE Channel
=============================================================================