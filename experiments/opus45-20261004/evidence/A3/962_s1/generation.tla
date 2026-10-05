---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES sbit,      \* sender's current bit
          abit,      \* sender's acknowledgement bit
          rbit,      \* receiver's bit
          sent,      \* data value being sent
          rcvd       \* data value received

vars == <<sbit, abit, rbit, sent, rcvd>>

TypeInvariant ==
    /\ sbit \in {0, 1}
    /\ abit \in {0, 1}
    /\ rbit \in {0, 1}
    /\ sent \in Data
    /\ rcvd \in Data

Init ==
    /\ sbit = 0
    /\ abit = 0
    /\ rbit = 1
    /\ sent \in Data
    /\ rcvd \in Data

\* Sender sends a new value when acknowledgement bit matches send bit
SendNew ==
    /\ abit = sbit
    /\ sent' \in Data
    /\ sbit' = 1 - sbit
    /\ UNCHANGED <<abit, rbit, rcvd>>

\* Receiver accepts a message when receive bit differs from sender bit
RcvMsg ==
    /\ rbit /= sbit
    /\ rcvd' = sent
    /\ rbit' = sbit
    /\ UNCHANGED <<sbit, abit, sent>>

\* Sender accepts an acknowledgement when receiver bit differs from sender acknowledgement bit
RcvAck ==
    /\ rbit /= abit
    /\ abit' = rbit
    /\ UNCHANGED <<sbit, rbit, sent, rcvd>>

Next ==
    \/ SendNew
    \/ RcvMsg
    \/ RcvAck

Fairness ==
    /\ WF_vars(RcvMsg)
    /\ WF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: type correctness
Safety == TypeInvariant

\* Liveness property: sender and acknowledgement bits are infinitely often out of sync
Liveness == []<>(sbit /= abit)

=============================================================================