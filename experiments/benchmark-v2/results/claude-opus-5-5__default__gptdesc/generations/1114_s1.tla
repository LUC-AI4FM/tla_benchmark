---------------------------- MODULE MCtcp ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the TCP specification in module tcp.         *)
(*                                                                         *)
(* Two peers are introduced. Node A has already performed an active open   *)
(* (state SYN-SENT) and node B has already performed a passive open        *)
(* (state LISTEN). An initial SYN segment is in the network toward B.      *)
(*                                                                         *)
(* To keep the state space finite for TLC:                                 *)
(*   - retransmission is forbidden: adjacent messages in a network         *)
(*     channel must differ (state constraint), and                         *)
(*   - no further ACTIVE_OPEN, PASSIVE_OPEN or SEND actions are allowed    *)
(*     after the initial setup (action constraints).                       *)
(*                                                                         *)
(* The constants, variables (tcb, connstate, network), Init, Next, vars    *)
(* and Spec come from module tcp. Each MC definition below is meant to be  *)
(* named in the TLC model configuration.                                   *)
(***************************************************************************)
EXTENDS tcp

CONSTANTS A, B

ASSUME A # B

\* Value to substitute for the constant Peers in the model.
MCPeers == {A, B}

-----------------------------------------------------------------------------
(* Initial state: A is in SYN-SENT after an active open, B is in LISTEN    *)
(* after a passive open, and a SYN segment is in flight toward B.          *)

MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = B THEN << "SYN" >> ELSE << >>]

MCNext == Next

MCSpec == MCInit /\ [][MCNext]_vars

-----------------------------------------------------------------------------
(* State constraint: forbid retransmission, so adjacent messages in any     *)
(* network channel must be distinct.                                       *)

NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

(* Action constraints: forbid any further user-initiated opens or sends     *)
(* after the initial setup.                                                *)

NoActiveOpen ==
    \A local, remote \in Peers : ~ ACTIVE_OPEN(local, remote)

NoPassiveOpen ==
    \A local, remote \in Peers : ~ PASSIVE_OPEN(local, remote)

NoSend ==
    \A local, remote \in Peers : ~ SEND(local, remote)

=============================================================================