---------------------------- MODULE ImprovedSDP ----------------------------
(***************************************************************************)
(* Improved Software Defined Perimeter (SDP) architecture.                 *)
(*                                                                         *)
(* Participants: a legitimate Client, an SDP Controller, a Firewall, a     *)
(* target Server, and a Dolev-Yao style Attacker.                          *)
(*                                                                         *)
(* An SPA (Single Packet Authorization) message carries an encrypted,      *)
(* authenticated 4-tuple <cip, cport, sip, sport> describing the exact     *)
(* data-plane TCP connection the client intends to open, plus a nonce.     *)
(* After successful authentication, the controller configures the         *)
(* firewall with an exact 4-tuple ACL rule.                                *)
(*                                                                         *)
(* The attacker can:                                                       *)
(*   - observe every SPA message on the network (interception),            *)
(*   - re-inject observed messages, possibly rewriting the cleartext       *)
(*     source address (replay / spoofing),                                 *)
(*   - forge SPA messages without the client's key,                        *)
(*   - send TCP SYN probes with arbitrary (also spoofed) 4-tuples.         *)
(* The attacker cannot read or modify the encrypted tuple or forge the     *)
(* client key.                                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    CIP,          \* IP address of the legitimate client
    AIP,          \* IP address of the attacker
    SIP,          \* IP address of the protected server
    SPort,        \* service port of the protected server
    Ports,        \* set of possible client source ports
    Nonces,       \* finite set of SPA nonces
    MaxRetrans    \* bound on TCP SYN losses / retransmissions

ASSUME /\ CIP # AIP
       /\ Ports # {}
       /\ Nonces # {}
       /\ MaxRetrans \in Nat

-----------------------------------------------------------------------------
(* Data domains *)

SrcIPs  == {CIP, AIP}

Tuples  == [cip : SrcIPs, cport : Ports, sip : {SIP}, sport : {SPort}]

Keys    == {"K", "None"}     \* "K" = authenticated with client's secret key

SPAMsgs == [src : SrcIPs, nonce : Nonces, tuple : Tuples, key : Keys]

TCPPkts == [t : Tuples, from : {"client", "attacker"}]

Sessions == [nonce : Nonces, tuple : Tuples]

ClientStates == {"idle", "spaSent", "connecting", "connected"}

-----------------------------------------------------------------------------
VARIABLES
    net,            \* SPA messages in transit to the controller
    attackerKnows,  \* SPA messages observed by the attacker
    clientSent,     \* SPA messages genuinely sent by the client
    usedNonces,     \* nonces already accepted by the controller
    authSessions,   \* authenticated SPA sessions (nonce, tuple)
    acl,            \* firewall exact 4-tuple allow rules
    clientState,    \* client protocol state
    clientPort,     \* source port chosen by the client
    tcpNet,         \* TCP SYN packets in transit to the firewall
    serverConns,    \* 4-tuples for which the server accepted a connection
    attackerResp,   \* TRUE iff attacker ever received a server response
    retrans,        \* number of SYN retransmissions done by the client
    losses          \* number of SYN packets lost in the network

vars == << net, attackerKnows, clientSent, usedNonces, authSessions, acl,
           clientState, clientPort, tcpNet, serverConns, attackerResp,
           retrans, losses >>

ClientT == [cip |-> CIP, cport |-> clientPort, sip |-> SIP, sport |-> SPort]

ClientSyn == [t |-> ClientT, from |-> "client"]

-----------------------------------------------------------------------------
TypeOK ==
    /\ net \subseteq SPAMsgs
    /\ attackerKnows \subseteq SPAMsgs
    /\ clientSent \subseteq SPAMsgs
    /\ usedNonces \subseteq Nonces
    /\ authSessions \subseteq Sessions
    /\ acl \subseteq Tuples
    /\ clientState \in ClientStates
    /\ clientPort \in Ports
    /\ tcpNet \subseteq TCPPkts
    /\ serverConns \subseteq Tuples
    /\ attackerResp \in BOOLEAN
    /\ retrans \in 0..MaxRetrans
    /\ losses \in 0..MaxRetrans

Init ==
    /\ net = {}
    /\ attackerKnows = {}
    /\ clientSent = {}
    /\ usedNonces = {}
    /\ authSessions = {}
    /\ acl = {}
    /\ clientState = "idle"
    /\ clientPort \in Ports
    /\ tcpNet = {}
    /\ serverConns = {}
    /\ attackerResp = FALSE
    /\ retrans = 0
    /\ losses = 0

-----------------------------------------------------------------------------
(* Client actions *)

\* Client sends an SPA packet binding the nonce to its exact data-plane tuple.
\* Under Dolev-Yao, the attacker observes every message on the wire.
ClientSendSPA(n) ==
    /\ clientState = "idle"
    /\ LET m == [src |-> CIP, nonce |-> n, tuple |-> ClientT, key |-> "K"]
       IN /\ net' = net \cup {m}
          /\ clientSent' = clientSent \cup {m}
          /\ attackerKnows' = attackerKnows \cup {m}
    /\ clientState' = "spaSent"
    /\ UNCHANGED << usedNonces, authSessions, acl, clientPort, tcpNet,
                    serverConns, attackerResp, retrans, losses >>

\* After the firewall rule for its exact tuple is installed, the client
\* opens the TCP connection using exactly that tuple.
ClientSendSYN ==
    /\ clientState = "spaSent"
    /\ ClientT \in acl
    /\ tcpNet' = tcpNet \cup {ClientSyn}
    /\ clientState' = "connecting"
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientPort, serverConns, attackerResp, retrans,
                    losses >>

\* TCP retransmission of the SYN after loss, using the same 4-tuple.
ClientRetransmit ==
    /\ clientState = "connecting"
    /\ ClientSyn \notin tcpNet
    /\ ClientT \notin serverConns
    /\ retrans < MaxRetrans
    /\ tcpNet' = tcpNet \cup {ClientSyn}
    /\ retrans' = retrans + 1
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientState, clientPort, serverConns, attackerResp,
                    losses >>

ClientConnected ==
    /\ clientState = "connecting"
    /\ ClientT \in serverConns
    /\ clientState' = "connected"
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientPort, tcpNet, serverConns, attackerResp,
                    retrans, losses >>

-----------------------------------------------------------------------------
(* Controller *)

\* Valid SPA: authenticated with client key, fresh nonce (anti-replay),
\* and cleartext source matches the encrypted tuple (anti-spoof).
ValidSPA(m) ==
    /\ m.key = "K"
    /\ m.nonce \notin usedNonces
    /\ m.src = m.tuple.cip

ControllerProcess(m) ==
    /\ m \in net
    /\ net' = net \ {m}
    /\ IF ValidSPA(m)
         THEN /\ usedNonces' = usedNonces \cup {m.nonce}
              /\ authSessions' = authSessions \cup
                                   {[nonce |-> m.nonce, tuple |-> m.tuple]}
              /\ acl' = acl \cup {m.tuple}     \* exact 4-tuple rule
         ELSE UNCHANGED << usedNonces, authSessions, acl >>
    /\ UNCHANGED << attackerKnows, clientSent, clientState, clientPort, tcpNet,
                    serverConns, attackerResp, retrans, losses >>

-----------------------------------------------------------------------------
(* Firewall and server *)

\* Default-drop firewall: only packets matching an exact 4-tuple rule reach
\* the server. Non-matching packets are silently dropped (server hiding).
\* A server response is routed to the packet's cip; the attacker only
\* receives it if cip = AIP.
FirewallForward(p) ==
    /\ p \in tcpNet
    /\ tcpNet' = tcpNet \ {p}
    /\ IF p.t \in acl
         THEN /\ serverConns' = serverConns \cup {p.t}
              /\ attackerResp' = (attackerResp \/ p.t.cip = AIP)
         ELSE UNCHANGED << serverConns, attackerResp >>
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientState, clientPort, retrans, losses >>

\* Bounded network loss of TCP packets.
TCPLoss(p) ==
    /\ p \in tcpNet
    /\ losses < MaxRetrans
    /\ tcpNet' = tcpNet \ {p}
    /\ losses' = losses + 1
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientState, clientPort, serverConns, attackerResp,
                    retrans >>

-----------------------------------------------------------------------------
(* Dolev-Yao attacker *)

\* Replay an observed SPA message, possibly rewriting the cleartext source.
AttackerReplay(m, src) ==
    /\ m \in attackerKnows
    /\ net' = net \cup {[m EXCEPT !.src = src]}
    /\ UNCHANGED << attackerKnows, clientSent, usedNonces, authSessions, acl,
                    clientState, clientPort, tcpNet, serverConns,
                    attackerResp, retrans, losses >>

\* Forge an SPA message without the client's key.
AttackerForge(src, n, t) ==
    /\ net' = net \cup {[src |-> src, nonce |-> n, tuple |-> t, key |-> "None"]}
    /\ UNCHANGED << attackerKnows, clientSent, usedNonces, authSessions, acl,
                    clientState, clientPort, tcpNet, serverConns,
                    attackerResp, retrans, losses >>

\* Probe the server with an arbitrary (possibly spoofed) 4-tuple.
AttackerProbe(t) ==
    /\ tcpNet' = tcpNet \cup {[t |-> t, from |-> "attacker"]}
    /\ UNCHANGED << net, attackerKnows, clientSent, usedNonces, authSessions,
                    acl, clientState, clientPort, serverConns, attackerResp,
                    retrans, losses >>

-----------------------------------------------------------------------------
Next ==
    \/ \E n \in Nonces : ClientSendSPA(n)
    \/ ClientSendSYN
    \/ ClientRetransmit
    \/ ClientConnected
    \/ \E m \in net : ControllerProcess(m)
    \/ \E p \in tcpNet : FirewallForward(p)
    \/ \E p \in tcpNet : TCPLoss(p)
    \/ \E m \in attackerKnows, s \in SrcIPs : AttackerReplay(m, s)
    \/ \E s \in SrcIPs, n \in Nonces, t \in Tuples : AttackerForge(s, n, t)
    \/ \E t \in Tuples : AttackerProbe(t)

Fairness ==
    /\ WF_vars(\E n \in Nonces : ClientSendSPA(n))
    /\ WF_vars(ClientSendSYN)
    /\ WF_vars(ClientRetransmit)
    /\ WF_vars(ClientConnected)
    /\ \A m \in SPAMsgs : WF_vars(ControllerProcess(m))
    /\ \A p \in TCPPkts : WF_vars(FirewallForward(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* SPA authentication: every authenticated session originates from a
\* message genuinely produced by the legitimate client.
SPAAuthentication ==
    \A s \in authSessions :
        \E m \in clientSent : m.nonce = s.nonce /\ m.tuple = s.tuple

\* Anti-replay: each nonce authenticates at most one session.
AntiReplay ==
    /\ \A s1, s2 \in authSessions : s1.nonce = s2.nonce => s1 = s2
    /\ Cardinality(authSessions) = Cardinality(usedNonces)

\* Anti-spoof: no firewall rule ever admits the attacker's address.
AntiSpoof ==
    \A t \in acl : t.cip = CIP /\ t.cip # AIP

\* Server hiddenness: the attacker never receives any server response.
ServerHidden == attackerResp = FALSE

\* Firewall rule consistency: ACL rules are exactly the authenticated tuples.
FirewallConsistency ==
    acl = { s.tuple : s \in authSessions }

\* Firewall correctness (also under retransmission): the server only ever
\* accepts connections permitted by an exact rule, a connecting client's
\* tuple is always permitted, and retransmissions never create new rules.
FirewallCorrectness ==
    /\ serverConns \subseteq acl
    /\ clientState \in {"connecting", "connected"} => ClientT \in acl
    /\ Cardinality(acl) <= Cardinality(usedNonces)
    /\ retrans <= losses

Safety ==
    /\ TypeOK
    /\ SPAAuthentication
    /\ AntiReplay
    /\ AntiSpoof
    /\ ServerHidden
    /\ FirewallConsistency
    /\ FirewallCorrectness

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Successful SPA authentication eventually installs the client's rule.
SPALeadsToRule == (clientState = "spaSent") ~> (ClientT \in acl)

\* Legitimate user access availability.
LegitimateAccess == (clientState = "spaSent") ~> (clientState = "connected")

EventualAccess == <>(clientState = "connected")

\* Despite bounded packet loss, retransmission eventually gets through.
RetransmissionLiveness ==
    (clientState = "connecting") ~> (ClientT \in serverConns)

THEOREM Spec => []Safety
THEOREM Spec => (SPALeadsToRule /\ LegitimateAccess /\ EventualAccess
                 /\ RetransmissionLiveness)
=============================================================================