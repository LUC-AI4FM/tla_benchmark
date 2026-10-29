------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for FIFO/Channel.tla.  This module is a        *)
(* wrapper that applies type information through INSTANCE, so the original *)
(* Channel module stays free of tool-specific details.                     *)
(*                                                                         *)
(* Init, Next, Spec and TypeInvariant come from Channel through the        *)
(* INSTANCE statement:                                                     *)
(*   TypeInvariant == chan \in [val : Data, rdy : {0,1}, ack : {0,1}]      *)
(*   Init          == TypeInvariant /\ chan.ack = chan.rdy                 *)
(*   Next          == (\E d \in Data : Send(d)) \/ Rcv                     *)
(*   Spec          == Init /\ [][Next]_chan                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: { val: Int, rdy: Int, ack: Int };
    chan

INSTANCE Channel

\* A concrete value for the constant Data, for use in model checking
\* configurations (for example, ConstInit or a .cfg file).
DataVal == {0, 1, 2}

\* The safety invariant inherited from Channel.
Inv == TypeInvariant
=============================================================================