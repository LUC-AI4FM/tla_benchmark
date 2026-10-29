------------------------------ MODULE ABSpec ------------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit protocol.  It describes   *)
(* what the protocol must accomplish (data values passed from sender to    *)
(* receiver in order, tagged with an alternating bit), not how messages    *)
(* are transmitted or acknowledged over lossy channels.                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES sent,   \* the message the sender has most recently made available
          rcvd    \* the message the receiver has most recently accepted

vars == <<sent, rcvd>>

Bits == {0, 1}

Msg == [data : Data, bit : Bits]

TypeOK == /\ sent \in Msg
          /\ rcvd \in Msg

---------------------------------------------------------------------------
(* Both sender and receiver start out agreeing on the current message,    *)
(* with the bit initially set to 1.                                        *)
Init == /\ sent \in [data : Data, bit : {1}]
        /\ rcvd = sent

(* The sender may send a new value only when the receiver has caught up.  *)
(* The new message carries the complemented bit.                          *)
Send == /\ sent = rcvd
        /\ \E d \in Data :
              sent' = [data |-> d, bit |-> 1 - sent.bit]
        /\ UNCHANGED rcvd

(* The receiver accepts a new value only when the sender has made one     *)
(* available (signalled by a differing bit).                               *)
Rcv == /\ rcvd.bit # sent.bit
       /\ rcvd' = sent
       /\ UNCHANGED sent

Next == Send \/ Rcv

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Send)
        /\ WF_vars(Rcv)

---------------------------------------------------------------------------
(* Safety properties *)

(* The bit correctly encodes whether the receiver has caught up: equal    *)
(* bits iff the receiver holds exactly the sender's current message.      *)
BitSync == (sent.bit = rcvd.bit) <=> (sent = rcvd)

(* The receiver only ever holds a value that the sender sent: whenever    *)
(* the receiver's value changes, it becomes the sender's current message. *)
RcvOnlySent == [][rcvd' # rcvd => rcvd' = sent]_vars

(* Send-then-receive ordering: the sender and receiver never change       *)
(* simultaneously, and the sender only sends when the receiver caught up. *)
Ordering == [][ /\ (sent' # sent => (sent = rcvd /\ rcvd' = rcvd))
                /\ (rcvd' # rcvd => (sent # rcvd /\ sent' = sent)) ]_vars

Safety == TypeOK /\ BitSync

---------------------------------------------------------------------------
(* Liveness properties *)

(* The sender eventually sends new data, again and again. *)
SenderProgress == []<><<Send>>_vars

(* The receiver eventually receives the data, again and again. *)
ReceiverProgress == []<><<Rcv>>_vars

(* Whatever is sent is eventually received. *)
EventuallyReceived == (sent # rcvd) ~> (sent = rcvd)

Liveness == SenderProgress /\ ReceiverProgress /\ EventuallyReceived

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ BitSync)
THEOREM Spec => RcvOnlySent /\ Ordering
THEOREM Spec => Liveness
=============================================================================