------------------------------ MODULE ApaChannel ------------------------------
(***************************************************************************)
(* A thin wrapper around the Channel specification that adds Apalache     *)
(* type annotations. The Channel specification itself is left unchanged;  *)
(* its Init, Next, Spec and invariants are inherited via INSTANCE Channel. *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: [val: Int, rdy: Int, ack: Int];
    chan

\* The set of data values that may be transmitted over the channel.
\* @type: Set(Int);
DataVal == Data

(***************************************************************************)
(* The channel behavior (TypeInvariant, Init, Send, Rcv, Next, Spec) is    *)
(* obtained from the original Channel module through instantiation.        *)
(***************************************************************************)
INSTANCE Channel

=============================================================================