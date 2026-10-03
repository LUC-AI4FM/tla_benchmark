---------------------------- MODULE ABCSpec ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES sbit,      \* Sender's current bit
          abit,      \* Sender's acknowledgement bit
          rbit,      \* Receiver's current bit
          sent,      \* Data value being sent
          rcvd       \* Data value received

vars == <<sbit, abit, rbit, sent, rcvd>>

TypeInv == /\ sbit \in {0, 1}
           /\ abit \in {0, 1}
           /\ rbit \in {0, 1}
           /\ sent \in Data
           /\ rcvd \in Data

Init == /\ sbit = 0
        /\ abit = 1
        /\ rbit = 1
        /\ sent \in Data
        /\ rcvd \in Data

\* Sender sends a new value when acknowledgement bit matches send bit
SendNew == /\ abit = sbit
           /\ \E d \in Data : sent' = d
           /\ sbit' = 1 - sbit
           /\ UNCHANGED <<abit, rbit, rcvd>>

\* Receiver accepts message when receive bit differs from sender bit
RcvMsg == /\ rbit # sbit
          /\ rcvd' = sent
          /\ rbit' = sbit
          /\ UNCHANGED <<sbit, abit, sent>>

\* Sender accepts acknowledgement when receiver bit differs from sender ack bit
RcvAck == /\ rbit # abit
          /\ abit' = rbit
          /\ UNCHANGED <<sbit, rbit, sent, rcvd>>

Next == SendNew \/ RcvMsg \/ RcvAck

Fairness == /\ WF_vars(RcvMsg)
            /\ WF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Temporal property: sender bit and acknowledgement bit are infinitely often out of sync
Liveness == []<>(sbit # abit)

ABCSpec == Spec

=============================================================================