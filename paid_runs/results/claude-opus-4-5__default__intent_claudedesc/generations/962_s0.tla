-------------------------------- MODULE ABCorrectness --------------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES sVal, sAck, sBit, rVal, rBit

vars == <<sVal, sAck, sBit, rVal, rBit>>

TypeInvariant ==
    /\ sVal \in Data
    /\ rVal \in Data
    /\ sBit \in {0, 1}
    /\ sAck \in {0, 1}
    /\ rBit \in {0, 1}

Init ==
    /\ sVal \in Data
    /\ rVal \in Data
    /\ sBit = 0
    /\ sAck = 0
    /\ rBit = 0

Send ==
    /\ sAck = sBit
    /\ \E d \in Data:
        /\ sVal' = d
        /\ sBit' = 1 - sBit
    /\ UNCHANGED <<sAck, rVal, rBit>>

Receive ==
    /\ rBit # sBit
    /\ rVal' = sVal
    /\ rBit' = sBit
    /\ UNCHANGED <<sVal, sAck, sBit>>

Acknowledge ==
    /\ sAck # rBit
    /\ sAck' = rBit
    /\ UNCHANGED <<sVal, sBit, rVal, rBit>>

Next ==
    \/ Send
    \/ Receive
    \/ Acknowledge

Fairness ==
    /\ WF_vars(Receive)
    /\ WF_vars(Acknowledge)

Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []TypeInvariant

======================================================================================