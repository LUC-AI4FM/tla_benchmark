------------------------------ MODULE ApaChannel ------------------------------
(***************************************************************************)
(* Type-annotated wrapper for the Channel specification, intended for use  *)
(* with the Apalache model checker.  The definitions of the Channel module *)
(* are reproduced here so that this module is self-contained and parses   *)
(* with SANY.  Apalache type annotations are given in comments.            *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Str);
    Data

VARIABLE
    \* @type: { val: Str, rdy: Int, ack: Int };
    chan

\* Concrete instantiation of Data used for model checking.
DataVal == { "d1", "d2" }

-----------------------------------------------------------------------------
(***************************************************************************)
(* Definitions from the Channel module (asynchronous handshake protocol).  *)
(***************************************************************************)

TypeInvariant ==
    chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

\* Sender places value d on the channel and toggles rdy.
Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* Receiver acknowledges the value by toggling ack.
Rcv ==
    /\ chan.rdy /= chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Rcv

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================