---------------------------- MODULE ABCSpec ----------------------------
CONSTANT Data

VARIABLES sVal, sAck, sSnd, rVal, rBit

vars == <<sVal, sAck, sSnd, rVal, rBit>>

TypeInv == /\ sVal \in Data
           /\ sAck \in {0, 1}
           /\ sSnd \in {0, 1}
           /\ rVal \in Data
           /\ rBit \in {0, 1}

Init == /\ sVal \in Data
        /\ sAck = 0
        /\ sSnd = 0
        /\ rVal \in Data
        /\ rBit = 0

Send == /\ sAck = sSnd
        /\ sVal' \in Data
        /\ sSnd' = 1 - sSnd
        /\ UNCHANGED <<sAck, rVal, rBit>>

Receive == /\ rBit # sSnd
           /\ rVal' = sVal
           /\ rBit' = sSnd
           /\ UNCHANGED <<sVal, sAck, sSnd>>

Ack == /\ sAck # rBit
       /\ sAck' = rBit
       /\ UNCHANGED <<sVal, sSnd, rVal, rBit>>

Next == Send \/ Receive \/ Ack

Fairness == /\ WF_vars(Receive)
            /\ WF_vars(Ack)

ABCSpec == Init /\ [][Next]_vars /\ Fairness

=============================================================================