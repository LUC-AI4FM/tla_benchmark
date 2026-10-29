------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for FIFO/Channel.tla.                         *)
(*                                                                         *)
(* This module wraps the Channel specification. It declares the constant   *)
(* Data and the variable chan with Apalache types, and then defines the    *)
(* Channel specification over them. The definitions below repeat the       *)
(* contents of Channel.tla, so that this module parses on its own without  *)
(* the file being present. The equivalent wrapper form is:                 *)
(*                                                                         *)
(*     INSTANCE Channel                                                    *)
(*                                                                         *)
(* That form keeps the original Channel module free of tool-specific       *)
(* details.                                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLE
    \* @type: [val: DATUM, rdy: Int, ack: Int];
    chan

(***************************************************************************)
(* Concrete value for the constant Data, for model checking with Apalache. *)
(* Use DataVal in a ConstInit or configuration to instantiate Data.        *)
(***************************************************************************)
DataVal == { "1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM" }

\* Optional constant initialization predicate for Apalache (--cinit).
CInit == Data = DataVal

(***************************************************************************)
(* Channel specification (contents of Channel.tla).                        *)
(***************************************************************************)
TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

\* @type: DATUM => Bool;
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================