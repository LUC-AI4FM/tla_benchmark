------------------------------- MODULE ChannelSpec -------------------------------

CONSTANTS DataValues \* A finite set of possible data values

VARIABLES channelState \* The state of the channel

\* Define the initial state of the channel
Init == 
    /\ channelState = [data \in {} |-> CHOOSE d \in DataValues : TRUE, ready \in 0..1, ack \in 0..1]
    /\ channelState.ready = channelState.ack

\* Next-state relation for the sender action
Sender ==
    \/ /\ channelState.ready = channelState.ack
       /\ \E newData \in DataValues :
            channelState' = [channelState EXCEPT ![data] = newData, ![ready] = 1 - channelState.ready]
    \/ channelState' = channelState

\* Next-state relation for the receiver action
Receiver ==
    \/ /\ channelState.ready # channelState.ack
       /\ channelState' = [channelState EXCEPT ![ack] = 1 - channelState.ack]
    \/ channelState' = channelState

\* Define the next-state relation
Next == Sender \/ Receiver

\* Define the specification
Spec ==
    Init /\ [][Next]_<<channelState>>

\* Type invariant: channel state must have data in DataValues and ready/ack bits in {0, 1}
TypeInvariant ==
    \A s \in SUBSET States : 
        /\ s # {}
        => \A c \in s :
            /\ c.data \in DataValues
            /\ c.ready \in {0, 1}
            /\ c.ack \in {0, 1}

=============================================================================