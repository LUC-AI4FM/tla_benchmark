---------------------------- MODULE SDP_SPA ----------------------------
(***************************************************************************)
(* Software-Defined Perimeter (SDP) with Single Packet Authorization.     *)
(* Control plane: clients send SPA messages to the SDP controller.        *)
(* The controller authenticates them, detects and logs replays and        *)
(* spoofs, and installs short-lived ACL rules bound to the client's       *)
(* authenticated TCP 4-tuple.                                              *)
(* Data plane: the firewall forwards TCP SYNs only when they match an     *)
(* installed rule. Otherwise it drops and logs them. The protected server *)
(* accepts only forwarded connections.                                     *)
(* The attacker sniffs SPA traffic. It can replay, spoof, or forge SPA     *)
(* messages and can send TCP probes.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Key,                \* secret key shared by the legitimate client and controller
    ATTACKER_BASEPORT,  \* first source port used by the attacker
    USER_BASEPORT,      \* source port used by the legitimate client
    MATCH_ANY,          \* wildcard value usable in ACL rule fields
    NAT_FLAG,           \* TRUE: attacker shares the client's public IP (behind NAT)
    UNKNOWN_AUTH_ID,    \* an authentication id not registered at the controller
    ClientCfg,          \* [IP |-> .., AuthID |-> ..]
    AttackerCfg,        \* [IP |-> ..]
    SDPSvrCfg,          \* [IP |-> .., Port |-> ..]  SDP controller
    SvrCfg              \* [IP |-> .., Port |-> ..]  protected server

VARIABLES
    clientPc,       \* "idle" | "spaSent" | "authorized" | "synSent" | "connected"
    clientNonce,    \* last nonce used by the client
    spaNet,         \* queue of SPA packets in flight to the controller
    sniffed,        \* SPA packets observed by the attacker
    ctrlLastNonce,  \* highest accepted nonce (replay window)
    ctrlLog,        \* controller log of rejected SPA messages
    accepted,       \* number of SPA messages accepted
    acl,            \* installed ephemeral ACL rules
    tcpNet,         \* queue of TCP SYN packets in flight to the firewall
    fwLog,          \* firewall drop log
    svrConns,       \* connections established at the protected server
    attackerBudget  \* bounds the number of attacker actions

vars == <<clientPc, clientNonce, spaNet, sniffed, ctrlLastNonce, ctrlLog,
          accepted, acl, tcpNet, fwLog, svrConns, attackerBudget>>

MaxNonce    == 2
MaxQ        == 3
MaxAttack   == 2
RuleTTL     == 2
AttackerKey == "attacker_key"

AttackerSrcIP == IF NAT_FLAG = TRUE THEN ClientCfg.IP ELSE AttackerCfg.IP
AttackerPorts == {ATTACKER_BASEPORT, ATTACKER_BASEPORT + 1}

\* The MAC binds the key, identity, 4-tuple, and nonce together.
Mac(k, aid, s, sp, d, dp, n) == <<k, aid, s, sp, d, dp, n>>

SPAMsg(s, sp, aid, n, mac) ==
    [src |-> s, sport |-> sp, dst |-> SDPSvrCfg.IP, dport |-> SDPSvrCfg.Port,
     authId |-> aid, nonce |-> n, svcIp |-> SvrCfg.IP, svcPort |-> SvrCfg.Port,
     mac |-> mac]

FieldMatch(rf, pf) == rf = MATCH_ANY \/ rf = pf

RuleMatches(r, p) ==
    /\ FieldMatch(r.src, p.src)
    /\ FieldMatch(r.sport, p.sport)
    /\ FieldMatch(r.dst, p.dst)
    /\ FieldMatch(r.dport, p.dport)

-----------------------------------------------------------------------------
Init ==
    /\ clientPc = "idle"
    /\ clientNonce = 0
    /\ spaNet = <<>>
    /\ sniffed = {}
    /\ ctrlLastNonce = 0
    /\ ctrlLog = {}
    /\ accepted = 0
    /\ acl = {}
    /\ tcpNet = <<>>
    /\ fwLog = {}
    /\ svrConns = {}
    /\ attackerBudget = 0

(*************************** Legitimate client ****************************)
ClientSendSPA ==
    /\ clientPc = "idle"
    /\ clientNonce < MaxNonce
    /\ Len(spaNet) < MaxQ
    /\ LET n == clientNonce + 1
           m == SPAMsg(ClientCfg.IP, USER_BASEPORT, ClientCfg.AuthID, n,
                       Mac(Key, ClientCfg.AuthID, ClientCfg.IP, USER_BASEPORT,
                           SvrCfg.IP, SvrCfg.Port, n))
       IN /\ spaNet' = Append(spaNet, m)
          /\ sniffed' = sniffed \cup {m}
          /\ clientNonce' = n
    /\ clientPc' = "spaSent"
    /\ UNCHANGED <<ctrlLastNonce, ctrlLog, accepted, acl, tcpNet, fwLog,
                   svrConns, attackerBudget>>

ClientSendSyn ==
    /\ clientPc = "authorized"
    /\ Len(tcpNet) < MaxQ
    /\ tcpNet' = Append(tcpNet, [src |-> ClientCfg.IP, sport |-> USER_BASEPORT,
                                 dst |-> SvrCfg.IP, dport |-> SvrCfg.Port,
                                 owner |-> "client"])
    /\ clientPc' = "synSent"
    /\ UNCHANGED <<clientNonce, spaNet, sniffed, ctrlLastNonce, ctrlLog,
                   accepted, acl, fwLog, svrConns, attackerBudget>>

ClientDisconnect ==
    /\ clientPc = "connected"
    /\ clientPc' = "idle"
    /\ svrConns' = {c \in svrConns : c.owner # "client"}
    /\ UNCHANGED <<clientNonce, spaNet, sniffed, ctrlLastNonce, ctrlLog,
                   accepted, acl, tcpNet, fwLog, attackerBudget>>

(***************************** SDP controller *****************************)
CtrlRecvSPA ==
    /\ spaNet # <<>>
    /\ LET m     == Head(spaNet)
           valid == /\ m.dst = SDPSvrCfg.IP
                    /\ m.authId = ClientCfg.AuthID
                    /\ m.mac = Mac(Key, m.authId, m.src, m.sport,
                                   m.svcIp, m.svcPort, m.nonce)
           fresh == m.nonce > ctrlLastNonce
       IN IF valid /\ fresh
          THEN /\ acl' = acl \cup
                    {[src |-> m.src, sport |-> m.sport, dst |-> m.svcIp,
                      dport |-> m.svcPort, authId |-> m.authId,
                      nonce |-> m.nonce, ttl |-> RuleTTL]}
               /\ ctrlLastNonce' = m.nonce
               /\ accepted' = accepted + 1
               /\ clientPc' = IF clientPc = "spaSent" THEN "authorized"
                                                       ELSE clientPc
               /\ UNCHANGED ctrlLog
          ELSE /\ ctrlLog' = ctrlLog \cup
                    {[kind |-> IF valid THEN "replay" ELSE "spoof",
                      authId |-> m.authId, nonce |-> m.nonce, src |-> m.src]}
               /\ UNCHANGED <<acl, ctrlLastNonce, accepted, clientPc>>
    /\ spaNet' = Tail(spaNet)
    /\ UNCHANGED <<clientNonce, sniffed, tcpNet, fwLog, svrConns,
                   attackerBudget>>

(********************* Rule ageing (ephemeral ACLs) ***********************)
\* Time advances only while no legitimate handshake is in progress. This
\* models the requirement that a valid SPA is honoured within a bounded
\* window. Rules expire when their TTL reaches zero.
Tick ==
    /\ acl # {}
    /\ clientPc \notin {"authorized", "synSent"}
    /\ acl' = {[r EXCEPT !.ttl = r.ttl - 1] : r \in {x \in acl : x.ttl > 1}}
    /\ UNCHANGED <<clientPc, clientNonce, spaNet, sniffed, ctrlLastNonce,
                   ctrlLog, accepted, tcpNet, fwLog, svrConns, attackerBudget>>

(******************************* Firewall *********************************)
FwProcess ==
    /\ tcpNet # <<>>
    /\ LET p == Head(tcpNet)
           M == {r \in acl : RuleMatches(r, p)}
       IN IF M # {}
          THEN LET r == CHOOSE x \in M : TRUE
               IN /\ acl' = acl \ {r}          \* one-shot rule
                  /\ svrConns' = svrConns \cup
                       {[src |-> p.src, sport |-> p.sport, owner |-> p.owner]}
                  /\ clientPc' = IF p.owner = "client" THEN "connected"
                                                       ELSE clientPc
                  /\ UNCHANGED fwLog
          ELSE /\ fwLog' = fwLog \cup
                    {[src |-> p.src, sport |-> p.sport, owner |-> p.owner]}
               /\ clientPc' = IF p.owner = "client" /\ clientPc = "synSent"
                              THEN "idle" ELSE clientPc
               /\ UNCHANGED <<acl, svrConns>>
    /\ tcpNet' = Tail(tcpNet)
    /\ UNCHANGED <<clientNonce, spaNet, sniffed, ctrlLastNonce, ctrlLog,
                   accepted, attackerBudget>>

(******************************* Attacker *********************************)
AttackerUnchanged ==
    UNCHANGED <<clientPc, clientNonce, sniffed, ctrlLastNonce, ctrlLog,
                accepted, acl, fwLog, svrConns>>

AttackerReplay ==
    /\ attackerBudget < MaxAttack
    /\ Len(spaNet) < MaxQ
    /\ \E m \in sniffed : spaNet' = Append(spaNet, m)
    /\ attackerBudget' = attackerBudget + 1
    /\ UNCHANGED tcpNet
    /\ AttackerUnchanged

AttackerSpoof ==
    /\ attackerBudget < MaxAttack
    /\ Len(spaNet) < MaxQ
    /\ \E m \in sniffed :
         \/ spaNet' = Append(spaNet,
                 [m EXCEPT !.src = AttackerSrcIP, !.sport = ATTACKER_BASEPORT])
         \/ spaNet' = Append(spaNet, [m EXCEPT !.nonce = m.nonce + 1])
    /\ attackerBudget' = attackerBudget + 1
    /\ UNCHANGED tcpNet
    /\ AttackerUnchanged

AttackerForge ==
    /\ attackerBudget < MaxAttack
    /\ Len(spaNet) < MaxQ
    /\ \E aid \in {ClientCfg.AuthID, UNKNOWN_AUTH_ID}, n \in 1..MaxNonce :
         spaNet' = Append(spaNet,
            SPAMsg(AttackerSrcIP, ATTACKER_BASEPORT, aid, n,
                   Mac(AttackerKey, aid, AttackerSrcIP, ATTACKER_BASEPORT,
                       SvrCfg.IP, SvrCfg.Port, n)))
    /\ attackerBudget' = attackerBudget + 1
    /\ UNCHANGED tcpNet
    /\ AttackerUnchanged

AttackerProbe ==
    /\ attackerBudget < MaxAttack
    /\ Len(tcpNet) < MaxQ
    /\ \E sp \in AttackerPorts :
         tcpNet' = Append(tcpNet, [src |-> AttackerSrcIP, sport |-> sp,
                                   dst |-> SvrCfg.IP, dport |-> SvrCfg.Port,
                                   owner |-> "attacker"])
    /\ attackerBudget' = attackerBudget + 1
    /\ UNCHANGED spaNet
    /\ AttackerUnchanged

-----------------------------------------------------------------------------
Next ==
    \/ ClientSendSPA \/ ClientSendSyn \/ ClientDisconnect
    \/ CtrlRecvSPA \/ Tick \/ FwProcess
    \/ AttackerReplay \/ AttackerSpoof \/ AttackerForge \/ AttackerProbe

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(CtrlRecvSPA)
    /\ WF_vars(FwProcess)
    /\ WF_vars(ClientSendSyn)
    /\ WF_vars(Tick)

-----------------------------------------------------------------------------
(******************************** Safety **********************************)

\* The attacker never completes a handshake with the server, so the
\* server stays hidden from it.
SvrHidenProperty ==
    \A c \in svrConns : c.owner # "attacker"

\* Only the authenticated client tuple ever reaches data access.
DataAccessSafeLaw ==
    \A c \in svrConns :
        /\ c.owner = "client"
        /\ c.src = ClientCfg.IP
        /\ c.sport = USER_BASEPORT

\* Every installed rule is bound to an authenticated SPA and its 4-tuple.
SPASafeLaw ==
    \A r \in acl :
        /\ r.authId = ClientCfg.AuthID
        /\ r.src = ClientCfg.IP
        /\ r.sport = USER_BASEPORT
        /\ r.dst = SvrCfg.IP
        /\ r.dport = SvrCfg.Port
        /\ r.nonce <= clientNonce
        /\ r.nonce <= ctrlLastNonce

\* Rules are exact (no wildcards) and short-lived (bounded TTL).
FwRuleConsistentProperty ==
    \A r \in acl :
        /\ r.src # MATCH_ANY /\ r.sport # MATCH_ANY
        /\ r.dst # MATCH_ANY /\ r.dport # MATCH_ANY
        /\ r.ttl \in 1..RuleTTL

\* The firewall forwards only packets matching installed rules.
\* All forwarded connections are therefore legitimate.
FwCorrectProperty ==
    /\ \A c \in svrConns : c.owner = "client"
    /\ \A d \in fwLog : d \notin svrConns

\* Replayed or spoofed SPA messages never install rules or grow ACL state.
SPA_AntiDosProperty ==
    /\ accepted <= clientNonce
    /\ Cardinality(acl) <= 1
    /\ ctrlLastNonce <= clientNonce

(******************************* Liveness *********************************)

\* A fresh, valid SPA is eventually authorized by the controller.
SPA_AvailableProperty ==
    (clientPc = "spaSent") ~> (clientPc = "authorized")

\* A legitimate client that sent a fresh SPA eventually connects.
UserAccessAvailProperty ==
    (clientPc = "spaSent") ~> (clientPc = "connected")

\* Additional property: no permanent exposure, because installed rules
\* are eventually removed.
AclShortLived ==
    (acl # {}) ~> (acl = {})

=============================================================================