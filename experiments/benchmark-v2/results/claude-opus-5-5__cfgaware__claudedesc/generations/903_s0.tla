---------------------------- MODULE MC_Channel ----------------------------
(***************************************************************************)
(* Typed wrapper around the Channel specification (Specifying Systems,     *)
(* Lamport), with Apalache type annotations. The behavior of the Channel   *)
(* module is reproduced here so that this module is self-contained and     *)
(* keeps the original semantics.                                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(DATUM);
    Data

VARIABLE
    \* @type: { val: DATUM, rdy: Int, ack: Int };
    chan

\* Concrete two-element set of placeholder datum values for model checking
\* @type: Set(DATUM);
DataVal == { "1_OF_DATUM", "2_OF_DATUM" }

---------------------------------------------------------------------------
(***************************************************************************)
(* Definitions of the Channel module                                       *)
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

---------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
===========================================================================