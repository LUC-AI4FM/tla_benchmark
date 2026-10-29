---------------------------- MODULE MC_Channel ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a single-place asynchronous channel using a  *)
(* rdy/ack handshake. The behavior of the underlying Channel module is     *)
(* included inline so this module is self-contained.                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Str);
    Data

VARIABLE
    \* @type: { val: Str, rdy: Int, ack: Int };
    chan

\* Concrete two-element data set used for model checking
\* @type: Set(Str);
DataVal == {"d1", "d2"}

-----------------------------------------------------------------------------
(* Channel specification *)

TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

\* Sender places data d and signals readiness
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* Receiver reads the data and acknowledges receipt
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