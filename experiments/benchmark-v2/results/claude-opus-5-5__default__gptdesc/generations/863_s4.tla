------------------------------- MODULE ImprovedSDP -------------------------------
(***************************************************************************)
(* Improved Software Defined Perimeter (SDP) model.                        *)
(*                                                                         *)
(* Participants: a legitimate Client, an SDP Controller, a Firewall, a     *)
(* target Server, and a Dolev-Yao style Attacker. The attacker can         *)
(* intercept (observe) all SPA traffic, replay it, spoof IP headers, forge *)
(* packets with its own key, probe the server, and drop data-plane         *)
(* packets (a bounded number of times).                                    *)
(*                                                                         *)
(* SPA packets carry a nonce and the encrypted 4-tuple                     *)
(* <<srcIP, srcPort, dstIP, dstPort>> of the planned TCP connection. The   *)
(* tuple is protected by the client key "K_C", so the attacker can neither *)
(* read nor modify it. After successful authentication the controller      *)
(* installs an exact 4-tuple ACL rule in the firewall.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    ClientIP,        \* IP address of the legitimate client
    AttackerIP,      \* IP address of the attacker
    ServerIP,        \* IP address of the hidden server
    ServerPort,      \* service port of the server
    ClientPorts,     \* source ports the client may use
    AttackerPorts,   \* source ports the attacker may use
    MaxNonce,        \* bound on nonces
    MaxRetrans,      \* bound on client SYN retransmissions
    MaxDrops         \* bound on attacker-induced packet drops

ASSUME /\ ClientIP # AttackerIP
       /\ ServerIP \notin {ClientIP, AttackerIP}
       /\ ClientPorts # {}
       /\ AttackerPorts # {}
       /\ MaxNonce \in Nat /\ MaxNonce >= 1
       /\ MaxRetrans \in Nat
       /\ MaxDrops \in Nat
       /\ MaxDrops <= MaxRetrans

IPs       == {ClientIP, AttackerIP}
AllPorts  == ClientPorts \cup AttackerPorts
Nonces    == 1..MaxNonce
AllTuples == { <<s, p, ServerIP, ServerPort>> : s \in IPs, p \in AllPorts }
NoTuple   == <<"none">>
Keys      == {"K_C", "K_A"}
Origins   == {"client", "attacker"}

\* SPA packet: ip = plaintext IP header source (spoofable),
\* nonce / tuple are protected under key 'auth'; origin is a ghost field.
SPAMsgs == [ip : IPs, nonce : Nonces, auth : Keys, tuple : AllTuples, origin : Origins]

\* TCP SYN packet on the data plane (origin is a ghost field).
SynPkts == [tuple : AllTuples, origin : Origins]

Phases == {"idle", "spaSent", "authed", "synSent", "connected"}

VARIABLES
    spaNet,       \* SPA packets in transit to the controller
    spaLog,       \* all SPA packets ever sent (attacker knowledge)
    accepted,     \* SPA packets accepted by the controller
    rejected,     \* SPA packets rejected by the controller
    usedNonces,   \* nonces already consumed by the controller
    ackNet,       \* authentication acknowledgements (nonces) to client
    acl,          \* firewall exact 4-tuple ACL rules
    clientPhase,  \* client protocol phase
    clientNonce,  \* nonce used by the client
    clientTuple,  \* 4-tuple the client intends to use
    synChan,      \* SYN packets in transit to the firewall
    fwdLog,       \* SYN packets forwarded by the firewall
    fwDropped,    \* SYN packets silently dropped by the firewall
    serverQ,      \* SYN packets delivered to the server
    synAck,       \* tuples the server answered with SYN-ACK
    retrans,      \* number of client SYN retransmissions
    drops         \* number of attacker-induced drops

vars == << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
           clientPhase, clientNonce, clientTuple, synChan, fwdLog, fwDropped,
           serverQ, synAck, retrans, drops >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ spaNet \subseteq SPAMsgs
    /\ spaLog \subseteq SPAMsgs
    /\ accepted \subseteq SPAMsgs
    /\ rejected \subseteq SPAMsgs
    /\ usedNonces \subseteq Nonces
    /\ ackNet \subseteq Nonces
    /\ acl \subseteq AllTuples
    /\ clientPhase \in Phases
    /\ clientNonce \in 0..MaxNonce
    /\ clientTuple \in AllTuples \cup {NoTuple}
    /\ synChan \subseteq SynPkts
    /\ fwdLog \subseteq SynPkts
    /\ fwDropped \subseteq SynPkts
    /\ serverQ \subseteq SynPkts
    /\ synAck \subseteq AllTuples
    /\ retrans \in 0..MaxRetrans
    /\ drops \in 0..MaxDrops

Init ==
    /\ spaNet = {}
    /\ spaLog = {}
    /\ accepted = {}
    /\ rejected = {}
    /\ usedNonces = {}
    /\ ackNet = {}
    /\ acl = {}
    /\ clientPhase = "idle"
    /\ clientNonce = 0
    /\ clientTuple = NoTuple
    /\ synChan = {}
    /\ fwdLog = {}
    /\ fwDropped = {}
    /\ serverQ = {}
    /\ synAck = {}
    /\ retrans = 0
    /\ drops = 0

-----------------------------------------------------------------------------
(* Client actions *)

ClientSendSPA ==
    /\ clientPhase = "idle"
    /\ \E p \in ClientPorts, n \in Nonces :
         LET t == <<ClientIP, p, ServerIP, ServerPort>>
             m == [ip |-> ClientIP, nonce |-> n, auth |-> "K_C",
                   tuple |-> t, origin |-> "client"]
         IN /\ clientNonce' = n
            /\ clientTuple' = t
            /\ spaNet' = spaNet \cup {m}
            /\ spaLog' = spaLog \cup {m}
    /\ clientPhase' = "spaSent"
    /\ UNCHANGED << accepted, rejected, usedNonces, ackNet, acl, synChan,
                    fwdLog, fwDropped, serverQ, synAck, retrans, drops >>

ClientRecvAck ==
    /\ clientPhase = "spaSent"
    /\ clientNonce \in ackNet
    /\ clientPhase' = "authed"
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientNonce, clientTuple, synChan, fwdLog, fwDropped,
                    serverQ, synAck, retrans, drops >>

ClientSendSyn ==
    /\ clientPhase = "authed"
    /\ synChan' = synChan \cup {[tuple |-> clientTuple, origin |-> "client"]}
    /\ clientPhase' = "synSent"
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientNonce, clientTuple, fwdLog, fwDropped, serverQ,
                    synAck, retrans, drops >>

\* Timeout-driven retransmission of the same SYN (same 4-tuple).
ClientRetransmit ==
    /\ clientPhase = "synSent"
    /\ clientTuple \notin synAck
    /\ [tuple |-> clientTuple, origin |-> "client"] \notin synChan
    /\ retrans < MaxRetrans
    /\ synChan' = synChan \cup {[tuple |-> clientTuple, origin |-> "client"]}
    /\ retrans' = retrans + 1
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, fwdLog, fwDropped,
                    serverQ, synAck, drops >>

ClientRecvSynAck ==
    /\ clientPhase = "synSent"
    /\ clientTuple \in synAck
    /\ clientPhase' = "connected"
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientNonce, clientTuple, synChan, fwdLog, fwDropped,
                    serverQ, synAck, retrans, drops >>

-----------------------------------------------------------------------------
(* Controller: SPA verification, anti-replay, anti-spoof, ACL install *)

ValidSPA(m) ==
    /\ m.auth = "K_C"                 \* authentic: protected under client key
    /\ m.nonce \notin usedNonces      \* anti-replay
    /\ m.ip = m.tuple[1]              \* anti-spoof: header IP matches encrypted tuple

ControllerProcess(m) ==
    /\ m \in spaNet
    /\ spaNet' = spaNet \ {m}
    /\ IF ValidSPA(m)
         THEN /\ accepted'   = accepted \cup {m}
              /\ usedNonces' = usedNonces \cup {m.nonce}
              /\ ackNet'     = ackNet \cup {m.nonce}
              /\ acl'        = acl \cup {m.tuple}   \* exact 4-tuple rule
              /\ UNCHANGED rejected
         ELSE /\ rejected'   = rejected \cup {m}
              /\ UNCHANGED << accepted, usedNonces, ackNet, acl >>
    /\ UNCHANGED << spaLog, clientPhase, clientNonce, clientTuple, synChan,
                    fwdLog, fwDropped, serverQ, synAck, retrans, drops >>

-----------------------------------------------------------------------------
(* Firewall: default-drop, exact 4-tuple matching *)

FwProcess(p) ==
    /\ p \in synChan
    /\ synChan' = synChan \ {p}
    /\ IF p.tuple \in acl
         THEN /\ fwdLog'  = fwdLog \cup {p}
              /\ serverQ' = serverQ \cup {p}
              /\ UNCHANGED fwDropped
         ELSE /\ fwDropped' = fwDropped \cup {p}   \* silent drop: no reply
              /\ UNCHANGED << fwdLog, serverQ >>
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, synAck, retrans, drops >>

-----------------------------------------------------------------------------
(* Server: answers SYNs it receives (replies go to the tuple's source IP) *)

ServerProcess(p) ==
    /\ p \in serverQ
    /\ serverQ' = serverQ \ {p}
    /\ synAck' = synAck \cup {p.tuple}
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, synChan, fwdLog,
                    fwDropped, retrans, drops >>

-----------------------------------------------------------------------------
(* Dolev-Yao attacker *)

\* Replay any previously observed SPA packet.
AttackerReplaySPA ==
    /\ \E m \in spaLog : spaNet' = spaNet \cup {m}
    /\ UNCHANGED << spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, synChan, fwdLog,
                    fwDropped, serverQ, synAck, retrans, drops >>

\* Re-send an observed SPA packet with a spoofed IP header
\* (encrypted payload cannot be modified).
AttackerSpoofSPA ==
    /\ \E m \in spaLog, ip \in IPs :
         spaNet' = spaNet \cup {[m EXCEPT !.ip = ip]}
    /\ UNCHANGED << spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, synChan, fwdLog,
                    fwDropped, serverQ, synAck, retrans, drops >>

\* Forge a fresh SPA packet; attacker only owns key K_A.
AttackerForgeSPA ==
    /\ \E ip \in IPs, n \in Nonces, t \in AllTuples :
         spaNet' = spaNet \cup {[ip |-> ip, nonce |-> n, auth |-> "K_A",
                                 tuple |-> t, origin |-> "attacker"]}
    /\ UNCHANGED << spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, synChan, fwdLog,
                    fwDropped, serverQ, synAck, retrans, drops >>

\* Port-scan / probe the server from the attacker's own address.
AttackerProbe ==
    /\ \E p \in AttackerPorts :
         synChan' = synChan \cup
            {[tuple |-> <<AttackerIP, p, ServerIP, ServerPort>>, origin |-> "attacker"]}
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, fwdLog, fwDropped,
                    serverQ, synAck, retrans, drops >>

\* Send a SYN with spoofed client source address.
AttackerSpoofSyn ==
    /\ \E p \in ClientPorts :
         synChan' = synChan \cup
            {[tuple |-> <<ClientIP, p, ServerIP, ServerPort>>, origin |-> "attacker"]}
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, fwdLog, fwDropped,
                    serverQ, synAck, retrans, drops >>

\* Drop a data-plane packet (bounded), forcing retransmission.
AttackerDropSyn ==
    /\ drops < MaxDrops
    /\ \E p \in synChan : synChan' = synChan \ {p}
    /\ drops' = drops + 1
    /\ UNCHANGED << spaNet, spaLog, accepted, rejected, usedNonces, ackNet, acl,
                    clientPhase, clientNonce, clientTuple, fwdLog, fwDropped,
                    serverQ, synAck, retrans >>

-----------------------------------------------------------------------------
ClientNext ==
    \/ ClientSendSPA
    \/ ClientRecvAck
    \/ ClientSendSyn
    \/ ClientRetransmit
    \/ ClientRecvSynAck

AttackerNext ==
    \/ AttackerReplaySPA
    \/ AttackerSpoofSPA
    \/ AttackerForgeSPA
    \/ AttackerProbe
    \/ AttackerSpoofSyn
    \/ AttackerDropSyn

Next ==
    \/ ClientNext
    \/ \E m \in SPAMsgs : ControllerProcess(m)
    \/ \E p \in SynPkts : FwProcess(p)
    \/ \E p \in SynPkts : ServerProcess(p)
    \/ AttackerNext

Fairness ==
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(ClientRecvAck)
    /\ WF_vars(ClientSendSyn)
    /\ WF_vars(ClientRetransmit)
    /\ WF_vars(ClientRecvSynAck)
    /\ \A m \in SPAMsgs : WF_vars(ControllerProcess(m))
    /\ \A p \in SynPkts : WF_vars(FwProcess(p))
    /\ \A p \in SynPkts : WF_vars(ServerProcess(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Only packets authenticated with the client's key and created by the client are accepted.
SPAAuthentication ==
    \A m \in accepted : m.auth = "K_C" /\ m.origin = "client"

\* No nonce is accepted twice (replays are rejected).
AntiReplay ==
    /\ \A a, b \in accepted : a.nonce = b.nonce => a = b
    /\ \A m \in accepted : m.nonce \in usedNonces

\* Accepted SPA packets have a header IP matching the encrypted tuple;
\* the attacker never obtains a rule for its own address.
AntiSpoof ==
    /\ \A m \in accepted : m.ip = m.tuple[1]
    /\ \A t \in acl : t[1] # AttackerIP

\* The server never answers the attacker: it stays hidden.
ServerHiddenness ==
    /\ \A t \in synAck : t[1] # AttackerIP
    /\ \A p \in fwdLog : p.tuple[1] # AttackerIP

\* Firewall rules correspond exactly to successful authentications.
FirewallRuleConsistency ==
    /\ acl = { m.tuple : m \in accepted }
    /\ \A t \in acl : t[1] = ClientIP /\ t[3] = ServerIP /\ t[4] = ServerPort
    /\ Cardinality(acl) <= Cardinality(accepted)

\* Under retransmission, the firewall behaves correctly: it only forwards
\* rule-matching packets, never drops a legitimate (authorized) client SYN,
\* and the client's tuple is authorized whenever it is sending SYNs.
FirewallRetransmissionCorrectness ==
    /\ \A p \in fwdLog : p.tuple \in acl
    /\ \A p \in fwDropped : p.origin # "client"
    /\ clientPhase \in {"authed", "synSent", "connected"} => clientTuple \in acl
    /\ clientPhase = "connected" => clientTuple \in synAck

SafetyInvariant ==
    /\ TypeOK
    /\ SPAAuthentication
    /\ AntiReplay
    /\ AntiSpoof
    /\ ServerHiddenness
    /\ FirewallRuleConsistency
    /\ FirewallRetransmissionCorrectness

\* ACL rules are never removed or altered in a way that breaks sessions.
AclMonotone == [][acl \subseteq acl']_vars

\* Nonces once used remain used (replay protection is permanent).
NoncesMonotone == [][usedNonces \subseteq usedNonces']_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Legitimate user eventually gains access to the server.
LegitimateAccess == <>(clientPhase = "connected")

\* A sent SPA eventually results in an installed exact ACL rule.
SPALeadsToRule ==
    (clientPhase = "spaSent") ~> (clientTuple \in acl)

\* Once authorized, the client's connection is eventually established
\* despite (bounded) packet loss and retransmissions.
RuleLeadsToConnection ==
    (clientPhase \in {"authed", "synSent"}) ~> (clientPhase = "connected")

\* Once connected, the client stays connected.
ConnectionStable ==
    [](clientPhase = "connected" => [](clientPhase = "connected"))

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => AclMonotone /\ NoncesMonotone
THEOREM Spec => LegitimateAccess /\ SPALeadsToRule /\ RuleLeadsToConnection /\ ConnectionStable
=============================================================================