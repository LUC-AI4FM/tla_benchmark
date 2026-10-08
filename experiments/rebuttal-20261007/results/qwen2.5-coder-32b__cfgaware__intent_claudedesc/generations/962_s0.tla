---- MODULE ABCSpec ----

CONSTANTS Data

VARIABLES sendBit, ackBit, recvBit, sendData, recvData

(*--algorithm AlternatingBitProtocol
variables 
    sendBit \in {0, 1} = 0,
    ackBit \in {0, 1} = 0,
    recvBit \in {0, 1} = 0,
    sendData \in Data,
    recvData \in Data;

begin
A:
    while TRUE do
        if sendBit = ackBit then
            with newSendData \in Data do
                sendBit := 1 - sendBit;
                sendData := newSendData;
            end with;
        else
            skip;
        end if;
        
        if recvBit # sendBit then
            recvData := sendData;
            recvBit := sendBit;
        else
            skip;
        end if;

        if ackBit # recvBit then
            ackBit := recvBit;
        else
            skip;
        end if;
    end while;
end algorithm;*)

TypeInv == /\ sendBit \in {0, 1}
           /\ ackBit \in {0, 1}
           /\ recvBit \in {0, 1}
           /\ sendData \in Data
           /\ recvData \in Data

Init == \/ /\ sendBit = 0
          /\ ackBit = 0
          /\ recvBit = 0
          /\ sendData \in Data
          /\ recvData \in Data

Send ==
    /\ sendBit = ackBit
    /\ \/ /\ sendBit' = 1 - sendBit
       /\ sendData' \in Data
       /\ UNCHANGED <<recvBit, recvData>>
    [] /\ UNCHANGED <<ackBit>>

Receive ==
    /\ recvBit # sendBit
    /\ recvData' = sendData
    /\ recvBit' = sendBit
    /\ UNCHANGED <<sendBit, ackBit, sendData>>

Acknowledge ==
    /\ ackBit # recvBit
    /\ ackBit' = recvBit
    /\ UNCHANGED <<sendBit, recvBit, sendData, recvData>>

Next == \/ Send
        \/ Receive
        \/ Acknowledge

Spec == Init /\ [][Next]_<<sendBit, ackBit, recvBit, sendData, recvData>> /\ WF_Recv /\ WF_Ack

WF_Recv == WF_RECEIVE(Receive)

WF_Ack == WF_RECEIVE(Acknowledge)

====