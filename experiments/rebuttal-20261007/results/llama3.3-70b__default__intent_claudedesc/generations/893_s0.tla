```
MODULE Channel
EXTENDS Integers, FiniteSets
CONSTANTS DataValues
VARIABLES channel

Init == 
  /\ channel = [data |-> ChooseData, senderReady |-> 0, receiverAck |-> 0]
  /\ ChooseData \in DataValues

Next == 
  \/ /\ channel.senderReady = channel.receiverAck
     /\ channel' = [channel EXCEPT !.senderReady = 1 - channel.senderReady, !.data = ChooseData]
     /\ ChooseData \in DataValues
  \/ /\ channel.senderReady # channel.receiverAck
     /\ channel' = [channel EXCEPT !.receiverAck = 1 - channel.receiverAck]

Spec == Init /\ [][Next]_channel

TypeInvariant == 
  /\ channel \in [data : DataValues, senderReady : {0, 1}, receiverAck : {0, 1}]

THEOREM Spec => []TypeInvariant
```
To check the invariant with three concrete data values, instantiate `DataValues` as `{a, b, c}` and run model checking. 

```
CONSTANT DataValues = {a, b, c}
```