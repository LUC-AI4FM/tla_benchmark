------------------------------- MODULE AlternatingBitProtocol -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sentData, receivedData

Init == /\ sendBit = 0 
        /\ ackBit = 0 
        /\ recvBit = 0 
        /\ sentData \in DataValues
        /\ receivedData \notin DataValues

Next == \/ /\ sendBit = ackBit
            /\ sentData' \in DataValues \ {sentData}
            /\ sendBit' = 1 - sendBit
            /\ UNCHANGED <<ackBit, recvBit, receivedData>>
         \/ /\ recvBit # sendBit
            /\ receivedData' = sentData
            /\ recvBit' = 1 - recvBit
            /\ UNCHANGED <<sendBit, ackBit, sentData>>
         \/ /\ recvBit # ackBit
            /\ ackBit' = 1 - ackBit
            /\ UNCHANGED <<sendBit, recvBit, sentData, receivedData>>

Spec == Init /\ [][Next]_<<sendBit, ackBit, recvBit, sentData, receivedData>>

TypeInvariant == /\ sendBit \in {0, 1}
                 /\ ackBit \in {0, 1}
                 /\ recvBit \in {0, 1}
                 /\ sentData \in DataValues
                 /\ (receivedData \in DataValues \/ receivedData \notin DataValues)

SafetyProperties == TypeInvariant

LivenessProperties == <>[](sendBit # ackBit)

FairnessAssumptions == WF_next(<<recvBit # sendBit>>, <<sendBit, ackBit, recvBit, sentData, receivedData>>) /\
                       WF_next(<<recvBit # ackBit>>, <<sendBit, ackBit, recvBit, sentData, receivedData>>)

CompleteSpec == Spec /\ SafetyProperties /\ LivenessProperties /\ FairnessAssumptions
=====================================================================================