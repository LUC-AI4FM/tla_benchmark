---------------------------- MODULE MCtcp ----------------------------
EXTENDS tcp

CONSTANTS A, B

MCPeers == {A, B}

-----------------------------------------------------------------------------
(* A starts in SYN-SENT after an active open, and B starts in LISTEN after *)
(* a passive open. The initial SYN segment is in the network toward B.     *)
MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = A THEN <<>> ELSE <<"SYN">>]

MCSpec == MCInit /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint: forbid retransmission. Adjacent messages in each      *)
(* channel must differ.                                                    *)
NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

(* Action constraint: a real system allows unboundedly many active opens,  *)
(* passive opens and sends. An explicit-state model checker such as TLC    *)
(* cannot enumerate infinitely many states. The initial active and passive *)
(* opens are implicit in MCInit, so no further opens or sends are allowed. *)
SingleActiveOpen ==
    ~ \E local, remote \in Peers :
        \/ ACTIVE_OPEN(local, remote)
        \/ PASSIVE_OPEN(local, remote)
        \/ SEND(local, remote)

=============================================================================