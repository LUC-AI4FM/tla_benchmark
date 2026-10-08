---------------------------- MODULE Channel ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Data
VARIABLE channelData, ready, ack

Init == (channelData \in Data) /\ (ready = 0) /\ (ack = 0)

Send(data) == (ready = ack) /\ 
              channelData' = data /\ 
              ready' = 1 - ready /\ 
              ack' = ack

Receive == (ready # ack) /\ 
           ready' = ready /\ 
           ack' = ready /\ 
           UNCHANGED channelData

Next == (\E data \in Data : Send(data)) \/ Receive

Spec == Init /\ [][Next]_<<channelData, ready, ack>>

TypeInvariant == channelData \in Data /\ (ready \in {0, 1}) /\ (ack \in {0, 1})

THEOREM Spec => []TypeInvariant
=============================================================================