------------------------------- MODULE MCtcp -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the TCP specification in module tcp.         *)
(*                                                                         *)
(* Two peers A and B are introduced. In the initial state, A has done an    *)
(* active open and is in SYN-SENT. B has done a passive open and is in      *)
(* LISTEN. A single SYN segment is in the network toward B.                 *)
(*                                                                         *)
(* Extra constraints keep the state space finite for TLC:                  *)
(*  - No retransmission: adjacent messages in a channel must differ.       *)
(*  - No further ACTIVE_OPEN, PASSIVE_OPEN or SEND after the setup.        *)
(***************************************************************************)
EXTENDS tcp, TLC, Sequences, Naturals

CONSTANTS A, B

ASSUME A # B

(* Constant override for tcp's Peers: Peers <- MCPeers *)
MCPeers == {A, B}

-----------------------------------------------------------------------------
(* Initial state: A actively opened toward B, B passively opened.          *)

MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = B THEN << "SYN" >> ELSE << >>]

-----------------------------------------------------------------------------
(* State constraint: no retransmission.                                    *)
(* Adjacent messages in each channel must differ.                          *)

NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

(* Action constraints: no further opens or sends after the initial setup.  *)

NoActiveOpen ==
    ~ \E local, remote \in Peers : ACTIVE_OPEN(local, remote)

NoPassiveOpen ==
    ~ \E local, remote \in Peers : PASSIVE_OPEN(local, remote)

NoSend ==
    ~ \E local, remote \in Peers : SEND(local, remote)

MCActionConstraint ==
    /\ NoActiveOpen
    /\ NoPassiveOpen
    /\ NoSend

-----------------------------------------------------------------------------
(* Next-state relation and specification used for model checking.          *)

MCNext ==
    /\ Next
    /\ MCActionConstraint
    /\ NoRetransmission'

MCSpec ==
    /\ MCInit
    /\ NoRetransmission
    /\ [][MCNext]_vars
    /\ WF_vars(MCNext)

-----------------------------------------------------------------------------
(* Properties to check: the initial setup satisfies the constraints, and   *)
(* every reachable state satisfies NoRetransmission.                       *)

MCInvariant == NoRetransmission

MCTypeOK ==
    /\ DOMAIN connstate = Peers
    /\ DOMAIN network = Peers
    /\ DOMAIN tcb = Peers

THEOREM MCSpec => []MCInvariant
=============================================================================