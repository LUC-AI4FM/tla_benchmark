---------------------------- MODULE MC_Channel ----------------------------
(***************************************************************************)
(* Type-annotated wrapper for the asynchronous handshake Channel           *)
(* specification, intended for the Apalache model checker. The Channel     *)
(* definitions are written inline so that this module parses on its own   *)
(* with SANY. Apalache type annotations are kept in comments.              *)
(*                                                                         *)
(* Configuration (Apalache / TLC):                                         *)
(*   CONSTANT  Data <- DataVal                                             *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeInvariant                                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Set(Int);
    Data

VARIABLES
    \* @type: { val: Int, rdy: Int, ack: Int };
    chan

vars == << chan >>

(***************************************************************************)
(* Concrete instantiation of Data used for finite model checking.          *)
(***************************************************************************)
\* @type: Set(Int);
DataVal == {0, 1}

(***************************************************************************)
(* Channel specification (two-phase handshake protocol).                   *)
(***************************************************************************)
TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ chan.val \in Data
    /\ chan.rdy \in {0, 1}
    /\ chan.ack = chan.rdy

\* Sender transmits value d: allowed only when the last value was acknowledged.
\* @type: Int => Bool;
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* Receiver acknowledges the pending value.
Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================