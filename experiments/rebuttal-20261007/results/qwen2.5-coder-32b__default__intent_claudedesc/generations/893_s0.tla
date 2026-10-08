------------------------------- MODULE Channel -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataValues \* A finite set of possible data values

VARIABLES channelState \* Record containing data and handshake bits

Init == 
  /\ channelState = [data \in {} |-> CHOOSE d \in DataValues : TRUE, ready \in {0}, ack \in {0}]

Next ==
  \/ /\ channelState.ready = channelState.ack
     /\ \/ /\ channelState.ready = 0
            /\ \E newData \in DataValues :
               channelState' = [channelState EXCEPT !.data = newData, !.ready = 1]
        \/ /\ channelState.ready = 1
           /\ channelState' = [channelState EXCEPT !.ack = 1]
  \/ /\ channelState.ready # channelState.ack
     /\ channelState.ack = 1
     /\ channelState' = [channelState EXCEPT !.ready = 0, !.ack = 0]

Spec ==
  WF_vars(Next, <<channelState>>)
  /\ Init
  /\ [][Next]_<<channelState>>
  /\ <><TE>_\<<channelState>>

TypeInvariant ==
  /\ channelState.data \in DataValues
  /\ channelState.ready \in {0, 1}
  /\ channelState.ack \in {0, 1}

THEOREM Spec => []TypeInvariant

=============================================================================