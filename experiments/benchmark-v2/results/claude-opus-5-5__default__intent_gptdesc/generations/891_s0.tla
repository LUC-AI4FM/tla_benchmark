---------------------------- MODULE BitHandshake ----------------------------
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES
    rdy,    \* sender's one-bit ready line
    ack,    \* receiver's one-bit acknowledge line
    val,    \* data channel
    sent,   \* ghost: value most recently produced and announced by the sender
    rcvd    \* ghost: value most recently consumed by the receiver

vars == <<rdy, ack, val, sent, rcvd>>

-----------------------------------------------------------------------------
(* Derived notions *)

Pending  == rdy # ack   \* a value has been announced but not yet consumed
Consumed == rdy = ack   \* the last announced value has been consumed

-----------------------------------------------------------------------------
(* Initial condition: lines agree, channel holds a valid value *)

Init ==
    /\ rdy \in {0, 1}
    /\ ack = rdy
    /\ val \in Data
    /\ sent = val
    /\ rcvd = val

-----------------------------------------------------------------------------
(* Sender: when idle (rdy = ack), choose any new value and toggle ready.     *)
(* The sender may pick a different value on each attempt; while the         *)
(* handshake is idle it may present any value it likes, and it commits     *)
(* that value by flipping rdy.                                              *)

Send ==
    /\ rdy = ack
    /\ \E d \in Data :
        /\ val'  = d
        /\ sent' = d
    /\ rdy' = 1 - rdy
    /\ UNCHANGED <<ack, rcvd>>

(* Receiver: when a change on rdy is detected (rdy # ack), consume the      *)
(* value on the channel and toggle acknowledge.                             *)

Rcv ==
    /\ rdy # ack
    /\ rcvd' = val
    /\ ack'  = 1 - ack
    /\ UNCHANGED <<rdy, val, sent>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars /\ WF_vars(Rcv) /\ WF_vars(Send)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ rdy  \in {0, 1}
    /\ ack  \in {0, 1}
    /\ val  \in Data
    /\ sent \in Data
    /\ rcvd \in Data

\* Data integrity: while a transfer is pending, the channel holds exactly the
\* value the sender produced; once consumed, the receiver holds exactly that
\* value (no loss, no corruption).
DataIntegrity ==
    /\ Pending  => val  = sent
    /\ Consumed => rcvd = sent

\* Alternation of handshake bits correctly indicates pending vs. consumed.
HandshakeInv ==
    /\ Pending  <=> (ENABLED Rcv /\ ~ENABLED Send)
    /\ Consumed <=> (ENABLED Send /\ ~ENABLED Rcv)

\* Every value delivered by an acknowledge step is the value that was sent.
DeliveryCorrect == [][Rcv => rcvd' = sent]_vars

\* Absence of deadlock: some agent can always move; in particular a pending
\* value can always be acknowledged.
NoDeadlock ==
    /\ ENABLED Next
    /\ Pending => ENABLED Rcv

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every send is eventually acknowledged.
EventualAck == Pending ~> Consumed

\* Each specific value sent is eventually delivered.
EventualDelivery == \A d \in Data : (Pending /\ sent = d) ~> (Consumed /\ rcvd = d)

\* Transfers continue indefinitely.
RepeatedTransfers == []<>Pending /\ []<>Consumed

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ DataIntegrity /\ HandshakeInv /\ NoDeadlock)
THEOREM Spec => DeliveryCorrect
THEOREM Spec => EventualAck /\ EventualDelivery /\ RepeatedTransfers

=============================================================================