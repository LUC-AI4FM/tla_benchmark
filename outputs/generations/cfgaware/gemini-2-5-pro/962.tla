---------------- MODULE ABCSpec ----------------
EXTENDS Naturals, TLC

CONSTANT Data
ASSUME Data # {}

VARIABLES sbit, rbit, sabit, sval, rval

vars == <<sbit, rbit, sabit, sval, rval>>

TypeInv ==
    /\ sbit \in {0, 1}
    /\ rbit \in {0, 1}
    /\ sabit \in {0, 1}
    /\ sval \in Data
    /\ rval \in Data

Init ==
    /\ sbit = 0
    /\ rbit = 1
    /\ sabit = 0
    /\ sval \in Data
    /\ rval \in Data

SendNewValue ==
    /\ sabit = sbit
    /\ sbit' = 1 - sbit
    /\ sval' \in Data
    /\ UNCHANGED <<rbit, sabit, rval>>

ReceiveMessage ==
    /\ rbit /= sbit
    /\ rval' = sval
    /\ rbit' = 1 - rbit
    /\ UNCHANGED <<sbit, sabit, sval>>

ReceiveAck ==
    /\ sabit /= rbit
    /\ sabit' = rbit
    /\ UNCHANGED <<sbit, rbit, sval, rval>>

Next == SendNewValue \/ ReceiveMessage \/ ReceiveAck

Fairness == WF_vars(ReceiveMessage) /\ WF_vars(ReceiveAck)

Property == []<>(sabit /= sbit)

ABCSpec == Init /\ [][Next]_vars /\ Fairness

=============================================================================