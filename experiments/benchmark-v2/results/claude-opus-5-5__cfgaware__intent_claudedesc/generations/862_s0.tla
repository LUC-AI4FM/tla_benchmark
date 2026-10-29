---------------------------- MODULE SPA_Attack ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS SDPSvrCfg, NAT_FLAG, USER_BASEPORT, MATCH_ANY, UNKNOWN_AUTH_ID,
          AttackerCfg, ClientCfg, ATTACKER_BASEPORT, SvrCfg

\* ---------------- Model values (bound by configuration) ----------------
const_1645172937699121000 == [IP |-> "sdp_ip", Port |-> 5000, LoginID |-> "user1", Key |-> "key1"]
const_1645172937699122000 == TRUE
const_1645172937699123000 == 10000
const_1645172937699124000 == "any"
const_1645172937699125000 == "unknown_id"
const_1645172937699126000 == [IP |-> "attacker_ip", Key |-> "attacker_key"]
const_1645172937699127000 == [IP |-> "client_ip", LoginID |-> "user1", Key |-> "key1"]
const_1645172937699128000 == 20000
const_1645172937699129000 == [IP |-> "svr_ip", Port |-> 80]

VARIABLES uState,        \* legitimate client state
          channel,       \* network messages in flight
          fwRules,       \* gateway firewall rules
          usedNonces,    \* SDP server anti-replay store
          authLog,       \* ghost: successful SPA authorizations
          svrRecv,       \* ghost: data packets delivered to protected server
          attackerCaps,  \* SPA packets sniffed by attacker
          attackerSteps, \* bound on attacker activity
          attackerRecv   \* responses received by attacker

vars == <<uState, channel, fwRules, usedNonces, authLog, svrRecv,
          attackerCaps, attackerSteps, attackerRecv>>

MaxAttackerSteps == 3

\* Under NAT the attacker shares the client's public IP
AtkIP == IF NAT_FLAG THEN ClientCfg.IP ELSE AttackerCfg.IP

Msg(t, sip, sp, dip, dp, pr, id, k, n, ap, o) ==
    [type |-> t, sIP |-> sip, sPort |-> sp, dIP |-> dip, dPort |-> dp,
     proto |-> pr, loginID |-> id, key |-> k, nonce |-> n,
     allowPort |-> ap, origin |-> o]

MatchProto(rv, v) == rv = MATCH_ANY \/ rv = v

RuleMatches(r, m) ==
    /\ r.sIP = m.sIP
    /\ r.sPort = m.sPort
    /\ r.dIP = m.dIP
    /\ r.dPort = m.dPort
    /\ MatchProto(r.proto, m.proto)

ClientSPA ==
    Msg("SPA", ClientCfg.IP, USER_BASEPORT, SDPSvrCfg.IP, SDPSvrCfg.Port,
        "UDP", ClientCfg.LoginID, ClientCfg.Key, 1, USER_BASEPORT, "client")

ClientData ==
    Msg("DATA", ClientCfg.IP, USER_BASEPORT, SvrCfg.IP, SvrCfg.Port,
        "TCP", "none", "none", 0, 0, "client")

Init ==
    /\ uState = "Init"
    /\ channel = {}
    /\ fwRules = {}
    /\ usedNonces = {}
    /\ authLog = {}
    /\ svrRecv = {}
    /\ attackerCaps = {}
    /\ attackerSteps = 0
    /\ attackerRecv = {}

\* ---------------- Legitimate client ----------------
ClientSendSPA ==
    /\ uState = "Init"
    /\ uState' = "SpaSent"
    /\ channel' = channel \cup {ClientSPA}
    /\ UNCHANGED <<fwRules, usedNonces, authLog, svrRecv, attackerCaps,
                   attackerSteps, attackerRecv>>

ClientConnect ==
    /\ uState = "SpaSent"
    /\ \E r \in fwRules : RuleMatches(r, ClientData)
    /\ uState' = "DataSent"
    /\ channel' = channel \cup {ClientData}
    /\ UNCHANGED <<fwRules, usedNonces, authLog, svrRecv, attackerCaps,
                   attackerSteps, attackerRecv>>

ClientRecv ==
    /\ uState = "DataSent"
    /\ \E m \in channel :
         /\ m.type = "ACK"
         /\ m.dIP = ClientCfg.IP
         /\ m.dPort = USER_BASEPORT
         /\ channel' = channel \ {m}
    /\ uState' = "Done"
    /\ UNCHANGED <<fwRules, usedNonces, authLog, svrRecv, attackerCaps,
                   attackerSteps, attackerRecv>>

ClientNext == ClientSendSPA \/ ClientConnect \/ ClientRecv

\* ---------------- SDP server ----------------
ValidSPA(m) ==
    /\ m.loginID = SDPSvrCfg.LoginID
    /\ m.key = SDPSvrCfg.Key
    /\ m.nonce \notin usedNonces

ProcessSPA(m) ==
    /\ m.type = "SPA"
    /\ channel' = channel \ {m}
    /\ attackerCaps' = IF NAT_FLAG /\ m.origin = "client"
                         THEN attackerCaps \cup {m}
                         ELSE attackerCaps
    /\ IF ValidSPA(m)
         THEN /\ fwRules' = fwRules \cup
                   {[sIP |-> m.sIP, sPort |-> m.allowPort, dIP |-> SvrCfg.IP,
                     dPort |-> SvrCfg.Port, proto |-> MATCH_ANY]}
              /\ usedNonces' = usedNonces \cup {m.nonce}
              /\ authLog' = authLog \cup
                   {[loginID |-> m.loginID, sIP |-> m.sIP,
                     allowPort |-> m.allowPort, origin |-> m.origin]}
         ELSE \* silently dropped: no response (server stays hidden)
              UNCHANGED <<fwRules, usedNonces, authLog>>
    /\ UNCHANGED <<uState, svrRecv, attackerSteps, attackerRecv>>

SDPNext == \E m \in channel : ProcessSPA(m)

\* ---------------- Gateway / protected server ----------------
ProcessData(m) ==
    /\ m.type = "DATA"
    /\ IF \E r \in fwRules : RuleMatches(r, m)
         THEN /\ svrRecv' = svrRecv \cup {m}
              /\ channel' = (channel \ {m}) \cup
                   {Msg("ACK", SvrCfg.IP, SvrCfg.Port, m.sIP, m.sPort,
                        "TCP", "none", "none", 0, 0, "server")}
         ELSE /\ channel' = channel \ {m}
              /\ UNCHANGED svrRecv
    /\ UNCHANGED <<uState, fwRules, usedNonces, authLog, attackerCaps,
                   attackerSteps, attackerRecv>>

GatewayNext == \E m \in channel : ProcessData(m)

\* ---------------- Attacker ----------------
AttackerReplay ==
    /\ attackerSteps < MaxAttackerSteps
    /\ \E c \in attackerCaps :
         channel' = channel \cup
           {[c EXCEPT !.sIP = AtkIP, !.sPort = ATTACKER_BASEPORT,
                      !.origin = "attacker"]}
    /\ attackerSteps' = attackerSteps + 1
    /\ UNCHANGED <<uState, fwRules, usedNonces, authLog, svrRecv,
                   attackerCaps, attackerRecv>>

AttackerForge ==
    /\ attackerSteps < MaxAttackerSteps
    /\ \E id \in {UNKNOWN_AUTH_ID, ClientCfg.LoginID}, n \in {1, 2} :
         channel' = channel \cup
           {Msg("SPA", AtkIP, ATTACKER_BASEPORT, SDPSvrCfg.IP, SDPSvrCfg.Port,
                "UDP", id, AttackerCfg.Key, n, ATTACKER_BASEPORT, "attacker")}
    /\ attackerSteps' = attackerSteps + 1
    /\ UNCHANGED <<uState, fwRules, usedNonces, authLog, svrRecv,
                   attackerCaps, attackerRecv>>

AttackerAccess ==
    /\ attackerSteps < MaxAttackerSteps
    /\ channel' = channel \cup
         {Msg("DATA", AtkIP, ATTACKER_BASEPORT, SvrCfg.IP, SvrCfg.Port,
              "TCP", "none", "none", 0, 0, "attacker")}
    /\ attackerSteps' = attackerSteps + 1
    /\ UNCHANGED <<uState, fwRules, usedNonces, authLog, svrRecv,
                   attackerCaps, attackerRecv>>

AttackerRecv ==
    /\ \E m \in channel :
         /\ m.type = "ACK"
         /\ m.dPort = ATTACKER_BASEPORT
         /\ channel' = channel \ {m}
         /\ attackerRecv' = attackerRecv \cup {m}
    /\ UNCHANGED <<uState, fwRules, usedNonces, authLog, svrRecv,
                   attackerCaps, attackerSteps>>

AttackerNext == AttackerReplay \/ AttackerForge \/ AttackerAccess \/ AttackerRecv

Terminated ==
    /\ uState = "Done"
    /\ UNCHANGED vars

Next == ClientNext \/ SDPNext \/ GatewayNext \/ AttackerNext \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec
            /\ WF_vars(ClientNext)
            /\ WF_vars(SDPNext)
            /\ WF_vars(GatewayNext)

\* ---------------- Safety invariants ----------------
SPASafeLaw ==
    \A a \in authLog : a.origin = "client" /\ a.loginID = ClientCfg.LoginID

DataAccessSafeLaw ==
    \A m \in svrRecv : m.origin = "client"

\* ---------------- Temporal properties ----------------
SPA_AvailableProperty ==
    (uState = "SpaSent") ~> (\E a \in authLog : a.origin = "client")

SPA_AntiDosProperty ==
    <>[](\A m \in channel : m.type # "SPA")

UserAccessAvailProperty ==
    <>(uState = "Done")

SvrHidenProperty ==
    [](attackerRecv = {})

FwRuleConsistentProperty ==
    [](\A r \in fwRules :
         /\ r.sIP = ClientCfg.IP
         /\ r.sPort = USER_BASEPORT
         /\ r.dIP = SvrCfg.IP
         /\ r.dPort = SvrCfg.Port)

FwCorrectProperty ==
    [](\A r \in fwRules :
         \E a \in authLog :
           /\ a.origin = "client"
           /\ a.sIP = r.sIP
           /\ a.allowPort = r.sPort)

=============================================================================