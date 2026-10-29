---------------------------- MODULE ApaChannel ----------------------------
(***************************************************************************)
(* A thin wrapper around the Channel specification that adds Apalache     *)
(* type annotations without modifying the original Channel module.        *)
(* All channel behavior (TypeInvariant, Init, Send, Rcv, Next, Spec) is    *)
(* inherited unchanged through INSTANCE Channel.                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: [val: Int, rdy: Int, ack: Int];
    chan

\* The set of data values that may be carried on the channel.
\* @type: Set(Int);
DataVal == Data

\* Import the original Channel specification unchanged.
\* This brings Init, Next, Spec and TypeInvariant into scope.
INSTANCE Channel
=============================================================================