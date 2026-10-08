------------------------------- MODULE HandshakeChannel -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS ValueSet

VARIABLES ch

Init == /\ ch = [val |-> <<>>, rdy |-> 0, ack |-> 0]

Next ==
    \/ /\ ch.rdy = ch.ack
       /\ \E v \in ValueSet : ch' = [ch EXCEPT ![val] = v, ![rdy] = 1 - ch.rdy]
    \/ /\ ch.rdy # ch.ack
       /\ ch' = [ch EXCEPT ![ack] = 1 - ch.ack]

TypeInvariant ==
    /\ ch.val \in ValueSet \/ ch.val = <<>>
    /\ ch.rdy \in {0, 1}
    /\ ch.ack \in {0, 1}

Spec == Init /\ [][Next]_<<ch>> /\ WF_next(<<ch>>)

WF_next(vars) ==
    \A state \in StateSpace : Enabled(state) => \E next_state \in StateSpace : NextEnabled(state, next_state)
    
StateSpace == { ch \in [val: ValueSet \/ <<>>, rdy: {0, 1}, ack: {0, 1}] }

Enabled(state) ==
    \/ state.rdy = state.ack
    \/ state.rdy # state.ack

NextEnabled(state, next_state) ==
    \/ /\ state.rdy = state.ack
       /\ \E v \in ValueSet : next_state = [state EXCEPT ![val] = v, ![rdy] = 1 - state.rdy]
    \/ /\ state.rdy # state.ack
       /\ next_state = [state EXCEPT ![ack] = 1 - state.ack]

=============================================================================