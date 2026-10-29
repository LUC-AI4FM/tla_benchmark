------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for the Channel module used in several       *)
(* chapters of Specifying Systems.  The original wrapper declares the     *)
(* typed constant and variable and then writes                             *)
(*                                                                         *)
(*     INSTANCE Channel                                                    *)
(*                                                                         *)
(* Here the definitions of Channel are written out in full, so the module  *)
(* parses on its own without Channel.tla.  DataVal gives a concrete value  *)
(* for Data, for use in model checking.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLE
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    chan

\* A concrete value for Data, for model checking
\* (for example, through ConstInit or a TLC model override).
\* @type: Set(DATUM);
DataVal == { "1_OF_DATUM", "2_OF_DATUM", "3_OF_DATUM" }

\* @type: <<{ val: DATUM, rdy: Int, ack: Int }>>;
vars == << chan >>

-----------------------------------------------------------------------------
(* Definitions of the Channel module                                       *)

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