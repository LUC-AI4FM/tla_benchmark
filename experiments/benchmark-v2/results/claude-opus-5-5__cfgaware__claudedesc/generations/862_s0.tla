---------------------------- MODULE SPA_Attack_New ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS SDPSvrCfg,
          NAT_FLAG,
          USER_BASEPORT,
          MATCH_ANY,
          UNKNOWN_AUTH_ID,
          AttackerCfg,
          ClientCfg,
          ATTACKER_BASEPORT,
          SvrCfg

\* Constant value definitions bound by the model configuration
const_1645172937699121000 == [IP |-> 12, Port |-> 8000]
const_1645172937699122000 == TRUE
const_1645172937699123000 == 10000
const_1645172937699124000 == 0
const_1645172937699125000 == 99
const_1645172937699126000 == [SrcIp |-> 11]
const_1645172937699127000 == [SrcIp |-> 11, LoginID |-> 1, Key |-> 44]
const_1645172937699128000 == 20000
const_1645172937699129000 == [IP |-> 22, Port |-> 80]

VARIABLES net,              \* set of packets in flight
          fwRules,          \* firewall rules installed by SDP server
          usedNonce,        \* nonces already accepted (anti-replay)
          clientNonce,      \* number of SPA packets the client has sent
          clientSynSent,    \* client has attempted the TCP connection
          clientConnected,  \* client established connection to server
          sniffed,          \* packets observed by the attacker
          attackBudget,     \* bounds attacker activity
          svrConns,         \* connections accepted by the protected server
          sdpReplies        \* number of replies emitted by SDP server

vars == <<net, fwRules, usedNonce, clientNonce, clientSynSent,
          clientConnected, sniffed, attackBudget, svrConns, sdpReplies>>

MaxNonce   == 2
MaxAttacks == 3

\* Source ports after NAT translation
ClientPort   == IF NAT_FLAG THEN USER_BASEPORT + 1 ELSE USER_BASEPORT
AttackerPort == IF NAT_FLAG THEN ATTACKER_BASEPORT + 1 ELSE ATTACKER_BASEPORT

Pkt(k, sip, sp, dip, dp, lid, ky, n, ap, o) ==
    [kind |-> k, srcIp |-> sip, srcPort |-> sp, dstIp |-> dip, dstPort |-> dp,
     loginId |-> lid, key |-> ky, nonce |-> n, authPort |-> ap, owner |-> o]

Match(r, p) ==
    /\ r.srcIp = p.srcIp
    /\ (r.srcPort = MATCH_ANY \/ r.srcPort = p.srcPort)
    /\ r.dstIp = p.dstIp
    /\ r.dstPort = p.dstPort

ClientHasRule ==
    \E r \in fwRules :
        Match(r, Pkt("TCP", ClientCfg.SrcIp, ClientPort, SvrCfg.IP, SvrCfg.Port,
                     0, 0, 0, 0, "client"))

Init ==
    /\ net = {}
    /\ fwRules = {}
    /\ usedNonce = {}
    /\ clientNonce = 0
    /\ clientSynSent = FALSE
    /\ clientConnected = FALSE
    /\ sniffed = {}
    /\ attackBudget = MaxAttacks
    /\ svrConns = {}
    /\ sdpReplies = 0

-----------------------------------------------------------------------------
\* Legitimate client

ClientSendSPA ==
    /\ clientNonce < MaxNonce
    /\ ~ClientHasRule
    /\ ~\E p \in net : p.kind = "SPA" /\ p.owner = "client"
    /\ net' = net \cup {Pkt("SPA", ClientCfg.SrcIp, ClientPort, SDPSvrCfg.IP,
                           SDPSvrCfg.Port, ClientCfg.LoginID, ClientCfg.Key,
                           clientNonce + 1, ClientPort, "client")}
    /\ clientNonce' = clientNonce + 1
    /\ UNCHANGED <<fwRules, usedNonce, clientSynSent, clientConnected,
                   sniffed, attackBudget, svrConns, sdpReplies>>

ClientConnect ==
    /\ ClientHasRule
    /\ ~clientSynSent
    /\ net' = net \cup {Pkt("TCP", ClientCfg.SrcIp, ClientPort, SvrCfg.IP,
                           SvrCfg.Port, 0, 0, 0, 0, "client")}
    /\ clientSynSent' = TRUE
    /\ UNCHANGED <<fwRules, usedNonce, clientNonce, clientConnected,
                   sniffed, attackBudget, svrConns, sdpReplies>>

-----------------------------------------------------------------------------
\* Attacker (shares the client's source IP, may sniff and replay)

AttackerSniff ==
    /\ \E p \in net :
        /\ p.owner = "client"
        /\ p \notin sniffed
        /\ sniffed' = sniffed \cup {p}
    /\ UNCHANGED <<net, fwRules, usedNonce, clientNonce, clientSynSent,
                   clientConnected, attackBudget, svrConns, sdpReplies>>

AttackerSend(p) ==
    /\ attackBudget > 0
    /\ net' = net \cup {p}
    /\ attackBudget' = attackBudget - 1
    /\ UNCHANGED <<fwRules, usedNonce, clientNonce, clientSynSent,
                   clientConnected, sniffed, svrConns, sdpReplies>>

AttackerReplay ==
    \E p \in sniffed :
        /\ p.kind = "SPA"
        /\ AttackerSend([p EXCEPT !.srcIp = AttackerCfg.SrcIp,
                                  !.srcPort = AttackerPort,
                                  !.owner = "attacker"])

AttackerForgeSPA ==
    AttackerSend(Pkt("SPA", AttackerCfg.SrcIp, AttackerPort, SDPSvrCfg.IP,
                     SDPSvrCfg.Port, UNKNOWN_AUTH_ID, 0, MaxNonce + 1,
                     AttackerPort, "attacker"))

AttackerProbeSvr ==
    AttackerSend(Pkt("TCP", AttackerCfg.SrcIp, AttackerPort, SvrCfg.IP,
                     SvrCfg.Port, 0, 0, 0, 0, "attacker"))

AttackerProbeSDP ==
    AttackerSend(Pkt("TCP", AttackerCfg.SrcIp, AttackerPort, SDPSvrCfg.IP,
                     SDPSvrCfg.Port, 0, 0, 0, 0, "attacker"))

AttackerAct ==
    \/ AttackerSniff
    \/ AttackerReplay
    \/ AttackerForgeSPA
    \/ AttackerProbeSvr
    \/ AttackerProbeSDP

-----------------------------------------------------------------------------
\* SDP server: silently processes SPA packets, never replies

ValidSPA(p) ==
    /\ p.kind = "SPA"
    /\ p.loginId = ClientCfg.LoginID
    /\ p.loginId # UNKNOWN_AUTH_ID
    /\ p.key = ClientCfg.Key
    /\ p.nonce \notin usedNonce

SDPRecv ==
    \E p \in net :
        /\ p.dstIp = SDPSvrCfg.IP
        /\ p.dstPort = SDPSvrCfg.Port
        /\ net' = net \ {p}
        /\ IF ValidSPA(p)
             THEN /\ fwRules' = fwRules \cup
                        {[srcIp   |-> p.srcIp,
                          srcPort |-> IF NAT_FLAG THEN p.authPort ELSE MATCH_ANY,
                          dstIp   |-> SvrCfg.IP,
                          dstPort |-> SvrCfg.Port,
                          loginId |-> p.loginId]}
                  /\ usedNonce' = usedNonce \cup {p.nonce}
             ELSE UNCHANGED <<fwRules, usedNonce>>
        /\ UNCHANGED <<clientNonce, clientSynSent, clientConnected,
                       sniffed, attackBudget, svrConns, sdpReplies>>

\* Firewall in front of the protected server
SvrRecv ==
    \E p \in net :
        /\ p.dstIp = SvrCfg.IP
        /\ net' = net \ {p}
        /\ IF p.kind = "TCP" /\ \E r \in fwRules : Match(r, p)
             THEN /\ svrConns' = svrConns \cup
                        {[srcIp |-> p.srcIp, srcPort |-> p.srcPort,
                          dstIp |-> p.dstIp, dstPort |-> p.dstPort,
                          owner |-> p.owner]}
                  /\ clientConnected' = (clientConnected \/ p.owner = "client")
             ELSE UNCHANGED <<svrConns, clientConnected>>
        /\ UNCHANGED <<fwRules, usedNonce, clientNonce, clientSynSent,
                       sniffed, attackBudget, sdpReplies>>

Next ==
    \/ ClientSendSPA
    \/ ClientConnect
    \/ AttackerAct
    \/ SDPRecv
    \/ SvrRecv

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(ClientConnect)
    /\ WF_vars(SDPRecv)
    /\ WF_vars(SvrRecv)

-----------------------------------------------------------------------------
\* Safety invariants

SPASafeLaw ==
    \A r \in fwRules :
        /\ r.loginId = ClientCfg.LoginID
        /\ r.srcIp = ClientCfg.SrcIp

DataAccessSafeLaw ==
    \A c \in svrConns : c.owner = "client"

\* Properties

SPA_AvailableProperty ==
    <>(\E r \in fwRules : r.srcIp = ClientCfg.SrcIp)

SPA_AntiDosProperty ==
    [](Cardinality(fwRules) <= clientNonce)

UserAccessAvailProperty ==
    <>clientConnected

SvrHidenProperty ==
    [](/\ sdpReplies = 0
       /\ \A c \in svrConns : \E r \in fwRules : Match(r, c))

FwRuleConsistentProperty ==
    [](\A r \in fwRules : r.dstIp = SvrCfg.IP /\ r.dstPort = SvrCfg.Port)

FwCorrectProperty ==
    [](\A r \in fwRules :
         r.srcPort = (IF NAT_FLAG THEN ClientPort ELSE MATCH_ANY))

=============================================================================