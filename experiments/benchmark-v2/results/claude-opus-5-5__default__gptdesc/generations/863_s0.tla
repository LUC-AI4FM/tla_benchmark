```tla
 \in acl
        /\ [tuple |-> clientTuple] \in synackNet

Safety ==
    /\ TypeOK
    /\ SPAAuthentication
    /\ NoForgedAuthentication
    /\ AntiReplay
    /\ AntiSpoof
    /\ AttackerNeverAuthorized
    /\ ServerHidden
    /\ AttackerProbesDropped
    /\ FirewallRuleConsistency
    /\ FirewallForwardCorrect
    /\ FirewallRetransmissionCorrect
    /\ ClientConnectionSound

---------------------------------------------------------------------------
(* Temporal safety properties *)

\* Accepted nonces are never forgotten (replay window never reopens).
NoncesMonotone == [][usedNonces \subseteq usedNonces']_vars

\* Firewall rules are never silently removed or altered.
ACLMonotone == [][acl \subseteq acl']_vars

\* A newly installed rule always coincides with a new authentication.
RuleOnlyOnAuth ==
    [][\A r \in acl' \ acl :
          \E a \in authLog' \ authLog : a.tuple = r /\ a.key = Kc]_vars

---------------------------------------------------------------------------
(* Liveness properties *)

\* Legitimate user access: once the client sends its SPA, it eventually
\* connects, despite attacker replays, spoofs, forgeries and probes.
LegitimateAccess == (clientState = "spaSent") ~> (clientState = "connected")

EventuallyConnected == <>(clientState = "connected")

\* The client's SPA is eventually processed and authorized.
SPAEventuallyAuthorized ==
    (clientState = "spaSent") ~> (clientTuple \in acl)

\* Under retransmission, every client SYN is eventually forwarded.
RetransmissionForwarded ==
    \A s \in SYNMsgs :
        (s \in synNet /\ s.inj = "client") ~> (s \in fwForwarded)

\* Every forwarded SYN is eventually answered by the server.
ServerEventuallyResponds ==
    \A s \in SYNMsgs :
        (s \in fwForwarded) ~> ([tuple |-> s.tuple] \in synackNet)

\* Attacker probes are eventually (and permanently) dropped.
AttackerProbeEventuallyDropped ==
    \A s \in SYNMsgs :
        (s \in synNet /\ s.inj = "attacker" /\ s.tuple[1] = AIP)
            ~> (s \in fwDropped)

THEOREM Spec => []Safety
THEOREM Spec => LegitimateAccess /\ RetransmissionForwarded
=============================================================================
```