---------------------------- MODULE ApaChannel ----------------------------
(***************************************************************************)
(* A thin wrapper around the Channel specification that adds Apalache     *)
(* type annotations. The original Channel module is left unchanged; its   *)
(* definitions (TypeInvariant, Init, Send, Rcv, Next, Spec, ...) are      *)
(* inherited through the INSTANCE statement below.                        *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Set(DATA);
    Data

VARIABLE
    \* @type: [val: DATA, rdy: Int, ack: Int];
    chan

\* A typed helper that injects a data value into the uninterpreted type DATA.
\* @type: Str => DATA;
DataVal(s) == s

\* All channel behavior (Init, Next, Spec, TypeInvariant) comes from Channel.
INSTANCE Channel
=============================================================================