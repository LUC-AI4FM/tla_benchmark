---------------------------- MODULE AsyncHandshakeChannel ----------------------------
(***************************************************************************)
(* An asynchronous single-slot message channel implementing a two-way      *)
(* handshake for one-way data transfer.  The shared cell holds one data    *)
(* value (val) and two one-bit control signals: rdy (toggled by the        *)
(* sender) and ack (toggled by the receiver).                              *)
(*                                                                         *)
(* The channel is ready for a new message when rdy = ack.  A mismatch      *)
(* (rdy # ack) signals an outstanding, unacknowledged message.             *)
(*                                                                         *)
(* The history variables sent and rcvd are used only to state the safety   *)
(* and liveness properties.  sent is the last value written by the sender  *)
(* and rcvd is the last value read by the receiver.                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES
    val,    \* data value held in the shared cell
    rdy,    \* sender's control bit
    ack,    \* receiver's control bit
    sent,   \* history: last value written by the sender
    rcvd    \* history: last value read by the receiver

vars == <<val, rdy, ack, sent, rcvd>>

-----------------------------------------------------------------------------
(* Helper predicates *)

ChannelReady   == rdy = ack     \* no outstanding message
MessagePending == rdy # ack     \* a new message awaits the receiver

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ val  \in Data
    /\ rdy  \in BOOLEAN
    /\ ack  \in BOOLEAN
    /\ sent \in Data
    /\ rcvd \in Data

-----------------------------------------------------------------------------
(* Initial condition: control bits are synchronized, so there is no      *)
(* outstanding message.                                                  *)

Init ==
    /\ val  \in Data
    /\ rdy  \in BOOLEAN
    /\ ack  = rdy
    /\ sent = val
    /\ rcvd = val

-----------------------------------------------------------------------------
(* Sender: writes a nondeterministically chosen value and toggles rdy,   *)
(* but only when the channel is ready.                                   *)

SendVal(d) ==
    /\ ChannelReady
    /\ val'  = d
    /\ sent' = d
    /\ rdy'  = ~rdy
    /\ UNCHANGED <<ack, rcvd>>

Send == \E d \in Data : SendVal(d)

(* Receiver: detects a mismatch, reads the data without modifying it,    *)
(* and toggles ack to acknowledge receipt.                               *)

Rcv ==
    /\ MessagePending
    /\ rcvd' = val
    /\ ack'  = ~ack
    /\ UNCHANGED <<val, rdy, sent>>

Next == Send \/ Rcv

-----------------------------------------------------------------------------
(* Fairness: the sender keeps attempting to send, and the receiver does  *)
(* not ignore an enabled receive forever.                                *)

Fairness ==
    /\ WF_vars(Send)
    /\ WF_vars(Rcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Control bits always remain booleans.
ControlBitsBoolean == rdy \in BOOLEAN /\ ack \in BOOLEAN

\* While a message is outstanding, the cell holds exactly what was written.
DataIntegrity == MessagePending => val = sent

\* After an acknowledgement, the receiver read exactly what was written.
ReceivedCorrectly == ChannelReady => rcvd = sent

\* The sender only writes (toggles rdy or changes the data) when allowed.
SenderOnlyWritesWhenAllowed ==
    [][(rdy' # rdy \/ val' # val) => ChannelReady]_vars

\* The receiver only acknowledges when it has detected a message.
ReceiverOnlyAcksOnMessage ==
    [][(ack' # ack) => MessagePending]_vars

\* The data is not lost or overwritten between the write and the ack.
NoOverwriteOfUnacked ==
    [][MessagePending => (val' = val /\ sent' = sent)]_vars

\* The receiver never modifies the data in the cell.
ReceiverDoesNotModifyData ==
    [][(ack' # ack) => (val' = val)]_vars

\* Each step toggles at most one control bit.
OneBitPerStep ==
    [][~(rdy' # rdy /\ ack' # ack)]_vars

Safety ==
    /\ []TypeOK
    /\ []ControlBitsBoolean
    /\ []DataIntegrity
    /\ []ReceivedCorrectly
    /\ SenderOnlyWritesWhenAllowed
    /\ ReceiverOnlyAcksOnMessage
    /\ NoOverwriteOfUnacked
    /\ ReceiverDoesNotModifyData
    /\ OneBitPerStep

-----------------------------------------------------------------------------
(* Liveness properties *)

\* When the sender has sent a fixed value d, the receiver eventually
\* acknowledges it, having received exactly d.
SentValueEventuallyAcked ==
    \A d \in Data :
        (MessagePending /\ sent = d) ~> (ChannelReady /\ rcvd = d)

\* The receiver does not starve: a pending message is eventually acked.
NoReceiverStarvation == MessagePending ~> ChannelReady

\* The sender is not blocked forever: the channel becomes ready infinitely often.
ChannelEventuallyReady == []<>ChannelReady

\* Messages keep flowing: there is a pending message infinitely often.
ProgressInfinitelyOften == []<>MessagePending

Liveness ==
    /\ SentValueEventuallyAcked
    /\ NoReceiverStarvation
    /\ ChannelEventuallyReady
    /\ ProgressInfinitelyOften

-----------------------------------------------------------------------------
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================