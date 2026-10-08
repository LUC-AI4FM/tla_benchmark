------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* Asynchronous single-bit handshake protocol between a sender and         *)
(* receiver for reliable data transfer without a shared clock.             *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Data  \* The finite set of data values that can be transferred

VARIABLES
    ready,      \* Sender's ready bit (0 or 1)
    ack,        \* Receiver's acknowledge bit (0 or 1)
    dataChannel,\* Current value on the data channel
    sentData,   \* Last data value sent by sender (when ready was toggled)
    receivedData \* Last data value received by receiver (when ack was toggled)

vars == <<ready, ack, dataChannel, sentData, receivedData>>

Bits == {0, 1}

(***************************************************************************)
(* Type invariant: all variables stay within their domains                 *)
(***************************************************************************)
TypeOK ==
    /\ ready \in Bits
    /\ ack \in Bits
    /\ dataChannel \in Data
    /\ sentData \in Data
    /\ receivedData \in Data

(***************************************************************************)
(* Initial state: ready and ack are in consistent state (both 0),          *)
(* data channel holds a valid data value                                   *)
(***************************************************************************)
Init ==
    /\ ready = 0
    /\ ack = 0
    /\ dataChannel \in Data
    /\ sentData \in Data
    /\ receivedData \in Data

(***************************************************************************)
(* Sender action: When ready equals ack (no pending transfer), the sender  *)
(* may non-deterministically choose a new data value, place it on the      *)
(* data channel, and toggle the ready bit.                                 *)
(***************************************************************************)
Send ==
    /\ ready = ack                          \* No pending transfer
    /\ \E d \in Data:
        /\ dataChannel' = d                 \* Place new data on channel
        /\ sentData' = d                    \* Record what was sent
        /\ ready' = 1 - ready               \* Toggle ready bit
    /\ UNCHANGED <<ack, receivedData>>

(***************************************************************************)
(* Receiver action: When ready differs from ack (pending transfer), the    *)
(* receiver samples the data, records it, and toggles the acknowledge bit. *)
(***************************************************************************)
Receive ==
    /\ ready # ack                          \* Pending transfer exists
    /\ receivedData' = dataChannel          \* Sample and record the data
    /\ ack' = 1 - ack                       \* Toggle acknowledge bit
    /\ UNCHANGED <<ready, dataChannel, sentData>>

(***************************************************************************)
(* Next state relation: either sender or receiver takes a step             *)
(***************************************************************************)
Next == Send \/ Receive

(***************************************************************************)
(* Fairness: Both agents should make progress when enabled                 *)
(***************************************************************************)
Fairness == WF_vars(Send) /\ WF_vars(Receive)

(***************************************************************************)
(* Complete specification with fairness                                    *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* SAFETY INVARIANTS                                                       *)
(***************************************************************************)

(***************************************************************************)
(* Handshake state invariant: The alternation of ready and ack bits        *)
(* correctly indicates pending vs. consumed data.                          *)
(* - When ready = ack: no pending transfer (data consumed or initial)      *)
(* - When ready # ack: pending transfer (data waiting to be consumed)      *)
(***************************************************************************)
HandshakeStateInvariant ==
    \/ (ready = ack)    \* Idle state: no pending transfer
    \/ (ready # ack)    \* Busy state: transfer pending

(***************************************************************************)
(* Data integrity invariant: When there is a pending transfer              *)
(* (ready # ack), the data on the channel equals what the sender sent.     *)
(* After receiver acknowledges, receivedData equals what was sent.         *)
(***************************************************************************)
DataIntegrityInvariant ==
    /\ (ready # ack) => (dataChannel = sentData)
    /\ (ready = ack) => (receivedData = sentData)

(***************************************************************************)
(* Combined safety invariant                                               *)
(***************************************************************************)
SafetyInvariant ==
    /\ TypeOK
    /\ HandshakeStateInvariant
    /\ DataIntegrityInvariant

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

(***************************************************************************)
(* Absence of deadlock: It's always possible to make progress              *)
(***************************************************************************)
NoDeadlock == [](Send \/ Receive)

(***************************************************************************)
(* Eventual acknowledgement: If sender issues a new value (ready # ack),   *)
(* the receiver can eventually acknowledge it (ready = ack)                *)
(***************************************************************************)
EventualAcknowledgement == [](ready # ack => <>(ready = ack))

(***************************************************************************)
(* Eventual transfer: If sender is ready to send (ready = ack),            *)
(* eventually a transfer can occur                                         *)
(***************************************************************************)
EventualTransfer == [](ready = ack => <>(ready # ack))

(***************************************************************************)
(* Progress property: The system continues to make transfers               *)
(***************************************************************************)
Progress == []<>(ready # ack) /\ []<>(ready = ack)

(***************************************************************************)
(* Liveness: Every send is eventually acknowledged                         *)
(***************************************************************************)
Liveness == EventualAcknowledgement

=============================================================================