---------------------------- MODULE MCtcp ----------------------------
EXTENDS tcp, TLC

CONSTANTS A, B

\* Two peers participate in the model-checked TCP connection setup.
const_Peers == {A, B}

\* Initial state:
\*  - one node has received the active open command and is in SYN-SENT;
\*    its SYN segment is already in the network toward the listening node.
\*  - the other node has received the passive open command and is in LISTEN.
MCInit ==
    \E node \in Peers :
        /\ tcb = [p \in Peers |-> TRUE]
        /\ network = [p \in Peers |-> IF p = node THEN << >> ELSE << "SYN" >>]
        /\ connstate = [p \in Peers |-> IF p = node THEN "SYN-SENT" ELSE "LISTEN"]

MCNext == Next

MCSpec == MCInit /\ [][MCNext]_<<tcb, connstate, network>>

-----------------------------------------------------------------------------
\* State constraints that keep the state space finite for TLC.

\* Forbid retransmission: adjacent messages in each channel must differ.
NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

\* Forbid any further active opens after the initial setup.
NoActiveOpen ==
    \A local, remote \in Peers :
        ~ ENABLED ACTIVE_OPEN(local, remote)

\* Forbid any further passive opens after the initial setup.
NoPassiveOpen ==
    \A local, remote \in Peers :
        ~ ENABLED PASSIVE_OPEN(local, remote)

\* Forbid any user SEND after the initial setup.
NoSend ==
    \A local, remote \in Peers :
        ~ ENABLED SEND(local, remote)

StateConstraint ==
    /\ NoRetransmission
    /\ NoActiveOpen
    /\ NoPassiveOpen
    /\ NoSend

=============================================================================