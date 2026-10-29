------------------------------ MODULE SharedValueSystem ------------------------------
EXTENDS Naturals

(***************************************************************************)
(* Reusable sender/receiver protocol. Its parameter `val` is the external *)
(* datum. The system binds `val` to its own shared value when it          *)
(* instantiates this module.                                               *)
(***************************************************************************)
---------------------------------- MODULE Protocol ----------------------------------
CONSTANTS Data, NoVal
VARIABLES val,   \* external parameter: the datum being handed over
          rdy,   \* sender's toggle bit
          ack,   \* receiver's toggle bit
          rcvd   \* last value consumed by the receiver

pvars == <<val, rdy, ack, rcvd>>

PTypeOK ==
    /\ val  \in Data \cup {NoVal}
    /\ rdy  \in BOOLEAN
    /\ ack  \in BOOLEAN
    /\ rcvd \in Data \cup {NoVal}

PInit ==
    /\ val  = NoVal
    /\ rdy  = FALSE
    /\ ack  = FALSE
    /\ rcvd = NoVal

\* The sender may write a new value only when the previous one was acknowledged.
Send(d) ==
    /\ rdy = ack
    /\ val' = d
    /\ rdy' = ~rdy
    /\ UNCHANGED <<ack, rcvd>>

\* The receiver consumes the pending value.
Rcv ==
    /\ rdy # ack
    /\ rcvd' = val
    /\ ack'  = ~ack
    /\ UNCHANGED <<val, rdy>>

PNext == (\E d \in Data : Send(d)) \/ Rcv

PSpec == PInit /\ [][PNext]_pvars /\ WF_pvars(Rcv)

\* Protocol correctness invariant: when the channel is idle, the receiver
\* holds exactly the last value sent.
PInv == (rdy = ack) => (rcvd = val)

\* A pending value is never overwritten before being consumed.
PNoOverwrite == [][(val' # val) => (rdy = ack)]_pvars

\* Every pending value is eventually received.
PDelivery == \A d \in Data : (rdy # ack /\ val = d) ~> (rdy = ack /\ rcvd = d)
=====================================================================================