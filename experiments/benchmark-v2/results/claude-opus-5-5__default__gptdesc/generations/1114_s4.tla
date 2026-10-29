------------------------------- MODULE MCtcp -------------------------------
EXTENDS tcp

(***************************************************************************)
(* Model-checking wrapper for the TCP specification in module tcp.         *)
(* Two peers are introduced; Peers is meant to be overridden by MCPeers.   *)
(***************************************************************************)

CONSTANTS A, B

MCPeers == {A, B}

MCVars == <<tcb, connstate, network>>

(***************************************************************************)
(* One node starts in SYN-SENT (it already received the active OPEN call   *)
(* and has sent a SYN). The other starts in LISTEN (it already received    *)
(* the passive OPEN call). A single SYN is in flight toward the listener.  *)
(***************************************************************************)
MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ \E node \in Peers :
        /\ connstate = [p \in Peers |-> IF p = node THEN "SYN-SENT" ELSE "LISTEN"]
        /\ network   = [p \in Peers |-> IF p = node THEN << >> ELSE << "SYN" >>]

MCNext == Next

MCSpec == MCInit /\ [][MCNext]_MCVars /\ WF_MCVars(MCNext)

(***************************************************************************)
(* State constraint: no retransmission, i.e. adjacent messages in any      *)
(* channel must differ.                                                    *)
(***************************************************************************)
NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

(***************************************************************************)
(* Action constraints: after the initial setup, no further active opens,  *)
(* passive opens, or sends are permitted. This keeps the state space       *)
(* finite for TLC.                                                         *)
(***************************************************************************)
NoActiveOpen ==
    \A local, remote \in Peers :
        ~ ACTIVE_OPEN(local, remote)

NoPassiveOpen ==
    \A local, remote \in Peers :
        ~ PASSIVE_OPEN(local, remote)

NoSend ==
    \A local, remote \in Peers :
        ~ SEND(local, remote)

=============================================================================