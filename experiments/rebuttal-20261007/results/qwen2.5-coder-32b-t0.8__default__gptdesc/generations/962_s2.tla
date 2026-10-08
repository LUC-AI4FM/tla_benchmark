------------------------------ MODULE AltBitProtocol ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sentData, receivedData

Init == 
  /\ sendBit = FALSE
  /\ ackBit = FALSE
  /\ recvBit = FALSE
  /\ sentData \in DataValues
  /\ receivedData \in DataValues

Next ==
  \/ /\ sendBit = ackBit
     /\ \/ \E newData \in DataValues \ {sentData} : 
            /\ sentData' = newData
            /\ UNCHANGED <<recvBit, ackBit>>
        /\ \/ recvBit # sendBit'
           -> receivedData' = sentData
              /\ recvBit' = sendBit'
        /\ \/ recvBit = sendBit'
           -> UNCHANGED receivedData
              /\ recvBit' = sendBit'
  \/ /\ recvBit # sendBit
     /\ receivedData' = sentData
     /\ recvBit' = sendBit
     /\ UNCHANGED <<sendBit, ackBit, sentData>>
  \/ /\ recvBit # ackBit
     /\ ackBit' = recvBit
     /\ UNCHANGED <<sendBit, recvBit, sentData, receivedData>>

TypeInvariant ==
  /\ sendBit \in BOOLEAN
  /\ ackBit \in BOOLEAN
  /\ recvBit \in BOOLEAN
  /\ sentData \in DataValues
  /\ receivedData \in DataValues

Spec ==
  WF_vars(<<Next>>, <<sendBit, ackBit, recvBit, sentData, receivedData>>) /\
  Init /\ [][Next]_<<sendBit, ackBit, recvBit, sentData, receivedData>> /\ 
  TypeInvariant /\ <>(recvBit # sendBit) 

WF_vars(vars, actions) ==
  \A s \in S: \E t \in S: \E a \in actions:
    vars' = <<t>>_<<vars>> /\ [][a]_vars

=============================================================================