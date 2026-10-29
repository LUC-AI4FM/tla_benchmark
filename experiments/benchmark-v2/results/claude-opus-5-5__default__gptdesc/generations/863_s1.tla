------------------------------ MODULE ImprovedSDP ------------------------------
(***************************************************************************)
(* Improved Software Defined Perimeter (SDP) architecture.                 *)
(*                                                                         *)
(* Participants: a legitimate client, an SDP controller, a firewall, a     *)
(* target server, and a Dolev-Yao-style attacker.                          *)
(*                                                                         *)
(* Each SPA (Single Packet Authorization) packet carries:                  *)
(*   - a nonce;                                                            *)
(*   - an encrypted client/server 4-tuple for the data-plane connection;   *)
(*   - a MAC.                                                              *)
(* Only the client holds the key, so only the client can produce a valid   *)
(* MAC (auth = TRUE).                                                      *)
(*                                                                         *)
(* The attacker can do the following:                                      *)
(*   - observe every SPA packet;                                           *)
(*   - replay observed SPA packets;                                        *)
(*   - spoof the outer source IP of observed packets;                      *)
(*   - forge packets that carry no valid MAC;                              *)
(*   - probe the server with TCP SYNs, including SYNs with a spoofed       *)
(*     source IP.                                                          *)
(*                                                                         *)
(* After the controller accepts an SPA packet, it installs an exact        *)
(* 4-tuple ACL rule in the firewall.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    ClientIP, AttackerIP, ServerIP,   \* network addresses
    ClientPorts,                      \* source ports usable by the client
    AttackerPorts,                    \* source ports usable by the attacker
    ServerPort,                       \* protected service port
    Nonces,                           \* SPA nonce space
    MaxRetrans                        \* bound on TCP SYN retransmissions

ASSUME
    /\ ClientIP # AttackerIP
    /\ ClientIP # ServerIP
    /\ AttackerIP # ServerIP
    /\ ClientPorts # {}
    /\ Nonces # {}
    /\ MaxRetrans \in Nat

VARIABLES
    spaLog,        \* all SPA packets ever put on the wire (attacker knowledge)
    spaInFlight,   \* SPA packets pending at the controller
    usedNonces,    \* nonces already accepted by the controller (anti-replay)
    sessions,      \* authenticated SPA sessions [nonce, tuple]
    ctrlAck,       \* authorization acknowledgements sent to the client (tuples)
    acl,           \* firewall ACL: set of exact 4-tuples
    tcpInFlight,   \* SYN packets in the network towards the firewall
    delivered,     \* SYNs forwarded by the firewall to the server
    dropped,       \* SYNs dropped by the firewall
    responses,     \* SYN-ACKs sent by the server
    clientState,   \* client protocol state
    clientTuple,   \* tuple chosen by the client for its connection
    retrans        \* number of SYN retransmissions/losses so far

vars == << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
           tcpInFlight, delivered, dropped, responses,
           clientState, clientTuple, retrans >>

IPs   == {ClientIP, AttackerIP}
Ports == ClientPorts \cup AttackerPorts

Tuples == [srcIP : IPs, srcPort : Ports, dstIP : {ServerIP}, dstPort : {ServerPort}]

Replies == [srcIP : {ServerIP}, srcPort : {ServerPort}, dstIP : IPs, dstPort : Ports]

SPAPackets == [src : IPs, nonce : Nonces, tuple : Tuples, auth : BOOLEAN]

MkTuple(ip, p) == [srcIP |-> ip, srcPort |-> p, dstIP |-> ServerIP, dstPort |-> ServerPort]

ClientPkt(n, p) == [src |-> ClientIP, nonce |-> n, tuple |-> MkTuple(ClientIP, p), auth |-> TRUE]

Reply(s) == [srcIP |-> s.dstIP, srcPort |-> s.dstPort, dstIP |-> s.srcIP, dstPort |-> s.srcPort]

ClientStates == {"idle", "spaSent", "authorized", "synSent", "connected"}

TypeOK ==
    /\ spaLog \subseteq SPAPackets
    /\ spaInFlight \subseteq SPAPackets
    /\ usedNonces \subseteq Nonces
    /\ sessions \subseteq [nonce : Nonces, tuple : Tuples]
    /\ ctrlAck \subseteq Tuples
    /\ acl \subseteq Tuples
    /\ tcpInFlight \subseteq Tuples
    /\ delivered \subseteq Tuples
    /\ dropped \subseteq Tuples
    /\ responses \subseteq Replies
    /\ clientState \in ClientStates
    /\ clientTuple \in Tuples
    /\ retrans \in 0..MaxRetrans

-----------------------------------------------------------------------------
Init ==
    /\ spaLog = {}
    /\ spaInFlight = {}
    /\ usedNonces = {}
    /\ sessions = {}
    /\ ctrlAck = {}
    /\ acl = {}
    /\ tcpInFlight = {}
    /\ delivered = {}
    /\ dropped = {}
    /\ responses = {}
    /\ clientState = "idle"
    /\ clientTuple = MkTuple(ClientIP, CHOOSE p \in ClientPorts : TRUE)
    /\ retrans = 0

-----------------------------------------------------------------------------
(* Legitimate client *)

\* The client sends an SPA packet that carries the encrypted data-plane tuple.
ClientSendSPA(n, p) ==
    /\ clientState = "idle"
    /\ clientState' = "spaSent"
    /\ clientTuple' = MkTuple(ClientIP, p)
    /\ spaLog' = spaLog \cup {ClientPkt(n, p)}
    /\ spaInFlight' = spaInFlight \cup {ClientPkt(n, p)}
    /\ UNCHANGED << usedNonces, sessions, ctrlAck, acl, tcpInFlight,
                    delivered, dropped, responses, retrans >>

\* The client receives the controller's authorization for its tuple.
ClientAuthorized ==
    /\ clientState = "spaSent"
    /\ clientTuple \in ctrlAck
    /\ clientState' = "authorized"
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    tcpInFlight, delivered, dropped, responses,
                    clientTuple, retrans >>

\* The client opens a TCP connection using exactly the authenticated tuple.
ClientSendSYN ==
    /\ clientState = "authorized"
    /\ clientState' = "synSent"
    /\ tcpInFlight' = tcpInFlight \cup {clientTuple}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    delivered, dropped, responses, clientTuple, retrans >>

\* The client retransmits its SYN, keeping the same 4-tuple.
ClientRetransmit ==
    /\ clientState = "synSent"
    /\ clientTuple \notin tcpInFlight
    /\ Reply(clientTuple) \notin responses
    /\ retrans < MaxRetrans
    /\ retrans' = retrans + 1
    /\ tcpInFlight' = tcpInFlight \cup {clientTuple}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    delivered, dropped, responses, clientState, clientTuple >>

\* The client receives the server's SYN-ACK.
ClientReceive ==
    /\ clientState = "synSent"
    /\ Reply(clientTuple) \in responses
    /\ clientState' = "connected"
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    tcpInFlight, delivered, dropped, responses,
                    clientTuple, retrans >>

-----------------------------------------------------------------------------
(* SDP controller *)

\* The controller accepts an SPA packet only when all of these hold:
\*   - the MAC is valid;
\*   - the nonce is fresh;
\*   - the outer source IP matches the encrypted tuple's source IP.
SPAValid(pkt) ==
    /\ pkt.auth
    /\ pkt.nonce \notin usedNonces
    /\ pkt.src = pkt.tuple.srcIP

\* On acceptance, the controller installs an exact 4-tuple ACL rule.
ControllerProcess(pkt) ==
    /\ pkt \in spaInFlight
    /\ spaInFlight' = spaInFlight \ {pkt}
    /\ IF SPAValid(pkt)
         THEN /\ usedNonces' = usedNonces \cup {pkt.nonce}
              /\ sessions' = sessions \cup {[nonce |-> pkt.nonce, tuple |-> pkt.tuple]}
              /\ acl' = acl \cup {pkt.tuple}
              /\ ctrlAck' = ctrlAck \cup {pkt.tuple}
         ELSE UNCHANGED << usedNonces, sessions, acl, ctrlAck >>
    /\ UNCHANGED << spaLog, tcpInFlight, delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

-----------------------------------------------------------------------------
(* Firewall: default deny, forward only exact 4-tuple matches *)

FirewallProcess(syn) ==
    /\ syn \in tcpInFlight
    /\ tcpInFlight' = tcpInFlight \ {syn}
    /\ IF syn \in acl
         THEN /\ delivered' = delivered \cup {syn}
              /\ UNCHANGED dropped
         ELSE /\ dropped' = dropped \cup {syn}
              /\ UNCHANGED delivered
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    responses, clientState, clientTuple, retrans >>

-----------------------------------------------------------------------------
(* Server: answers only SYNs that the firewall delivered *)

ServerRespond(s) ==
    /\ s \in delivered
    /\ Reply(s) \notin responses
    /\ responses' = responses \cup {Reply(s)}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    tcpInFlight, delivered, dropped,
                    clientState, clientTuple, retrans >>

-----------------------------------------------------------------------------
(* Network loss. Loss is bounded so that retransmissions can recover. *)

NetworkLose(syn) ==
    /\ syn \in tcpInFlight
    /\ retrans < MaxRetrans
    /\ tcpInFlight' = tcpInFlight \ {syn}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

-----------------------------------------------------------------------------
(* Dolev-Yao attacker *)

\* Replay an observed SPA packet unchanged.
AttackerReplay(k) ==
    /\ k \in spaLog
    /\ spaInFlight' = spaInFlight \cup {k}
    /\ UNCHANGED << spaLog, usedNonces, sessions, ctrlAck, acl, tcpInFlight,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

\* Replay an observed SPA packet with the outer source IP rewritten.
AttackerSpoofSrc(k) ==
    /\ k \in spaLog
    /\ LET k2 == [k EXCEPT !.src = AttackerIP]
       IN /\ spaLog' = spaLog \cup {k2}
          /\ spaInFlight' = spaInFlight \cup {k2}
    /\ UNCHANGED << usedNonces, sessions, ctrlAck, acl, tcpInFlight,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

\* Forge an SPA packet with arbitrary contents. Without the key, the MAC
\* is invalid. Modifying the encrypted tuple also invalidates the MAC.
AttackerForgeSPA(src, n, t) ==
    /\ LET k == [src |-> src, nonce |-> n, tuple |-> t, auth |-> FALSE]
       IN /\ spaLog' = spaLog \cup {k}
          /\ spaInFlight' = spaInFlight \cup {k}
    /\ UNCHANGED << usedNonces, sessions, ctrlAck, acl, tcpInFlight,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

\* Probe the server from the attacker's own address.
AttackerProbe(p) ==
    /\ tcpInFlight' = tcpInFlight \cup {MkTuple(AttackerIP, p)}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

\* Probe the server with a spoofed client source address. Any reply goes
\* to the client, not to the attacker.
AttackerSpoofSYN(p) ==
    /\ tcpInFlight' = tcpInFlight \cup {MkTuple(ClientIP, p)}
    /\ UNCHANGED << spaLog, spaInFlight, usedNonces, sessions, ctrlAck, acl,
                    delivered, dropped, responses,
                    clientState, clientTuple, retrans >>

-----------------------------------------------------------------------------
ClientStep ==
    \/ \E n \in Nonces, p \in ClientPorts : ClientSendSPA(n, p)
    \/ ClientAuthorized
    \/ ClientSendSYN
    \/ ClientRetransmit
    \/ ClientReceive

AttackerStep ==
    \/ \E k \in spaLog : AttackerReplay(k)
    \/ \E k \in spaLog : AttackerSpoofSrc(k)
    \/ \E src \in IPs, n \in Nonces, t \in Tuples : AttackerForgeSPA(src, n, t)
    \/ \E p \in Ports : AttackerProbe(p)
    \/ \E p \in Ports : AttackerSpoofSYN(p)

Next ==
    \/ ClientStep
    \/ \E pkt \in spaInFlight : ControllerProcess(pkt)
    \/ \E syn \in tcpInFlight : FirewallProcess(syn)
    \/ \E s \in delivered : ServerRespond(s)
    \/ \E syn \in tcpInFlight : NetworkLose(syn)
    \/ AttackerStep

Fairness ==
    /\ WF_vars(\E n \in Nonces, p \in ClientPorts : ClientSendSPA(n, p))
    /\ WF_vars(ClientAuthorized)
    /\ WF_vars(ClientSendSYN)
    /\ WF_vars(ClientRetransmit)
    /\ WF_vars(ClientReceive)
    /\ \A n \in Nonces, p \in ClientPorts : WF_vars(ControllerProcess(ClientPkt(n, p)))
    /\ \A p \in ClientPorts : WF_vars(FirewallProcess(MkTuple(ClientIP, p)))
    /\ \A p \in ClientPorts : WF_vars(ServerRespond(MkTuple(ClientIP, p)))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* SPA authentication: every session stems from an authentic client SPA
\* packet whose tuple matches the session.
SPAAuthentication ==
    \A s \in sessions :
        \E k \in spaLog :
            /\ k.auth
            /\ k.src = ClientIP
            /\ k.nonce = s.nonce
            /\ k.tuple = s.tuple
            /\ s.tuple.srcIP = ClientIP

\* Anti-replay: a nonce yields at most one session.
AntiReplay ==
    /\ \A s1, s2 \in sessions : s1.nonce = s2.nonce => s1 = s2
    /\ \A s \in sessions : s.nonce \in usedNonces

\* Anti-spoof: no session or ACL rule ever authorizes an attacker address.
AntiSpoof ==
    /\ \A r \in acl : r.srcIP # AttackerIP
    /\ \A s \in sessions : s.tuple.srcIP # AttackerIP

\* Server hiddenness: attacker-originated SYNs never reach the server,
\* and the server never answers the attacker.
ServerHidden ==
    /\ \A s \in delivered : s.srcIP # AttackerIP
    /\ \A r \in responses : r.dstIP # AttackerIP

\* Firewall rule consistency: the ACL is exactly the set of authenticated
\* tuples, each being an exact 4-tuple towards the protected service.
FirewallConsistency ==
    /\ acl = {s.tuple : s \in sessions}
    /\ \A r \in acl : r.dstIP = ServerIP /\ r.dstPort = ServerPort
    /\ Cardinality(acl) <= Cardinality(sessions)

\* Firewall correctness under retransmissions:
\*   - only ACL-matching SYNs are delivered;
\*   - the client's tuple stays authorized while it (re)transmits;
\*   - the retransmission bound is respected.
FirewallCorrectness ==
    /\ delivered \subseteq acl
    /\ clientState \in {"authorized", "synSent", "connected"} => clientTuple \in acl
    /\ retrans <= MaxRetrans

SafetyInvariant ==
    /\ TypeOK
    /\ SPAAuthentication
    /\ AntiReplay
    /\ AntiSpoof
    /\ ServerHidden
    /\ FirewallConsistency
    /\ FirewallCorrectness

THEOREM Spec => []SafetyInvariant

-----------------------------------------------------------------------------
(* Liveness properties *)

\* An SPA packet sent by the client is eventually authenticated.
SPAEventuallyAuthenticated ==
    (clientState = "spaSent") ~> (clientTuple \in acl)

\* Legitimate user access availability: the client eventually connects.
LegitimateAccess == <>(clientState = "connected")

\* Under retransmission, a client that sent a SYN eventually connects.
RetransmissionLiveness == (clientState = "synSent") ~> (clientState = "connected")

\* Once connected, the client stays connected.
ConnectionStable == [](clientState = "connected" => [](clientState = "connected"))

THEOREM Spec => /\ SPAEventuallyAuthenticated
                /\ LegitimateAccess
                /\ RetransmissionLiveness
                /\ ConnectionStable
=============================================================================