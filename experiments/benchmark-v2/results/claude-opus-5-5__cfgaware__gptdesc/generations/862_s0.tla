------------------------------- MODULE MC -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS SDPSvrCfg, NAT_FLAG, USER_BASEPORT, MATCH_ANY, UNKNOWN_AUTH_ID,
          AttackerCfg, ClientCfg, ATTACKER_BASEPORT, SvrCfg

\* ---------------- Model parameter values (bound via the cfg) ----------------
const_1645172937699121000 == [IP |-> "10.0.0.1", Port |-> 5000]
const_1645172937699122000 == FALSE
const_1645172937699123000 == 10000
const_1645172937699124000 == 0
const_1645172937699125000 == 0
const_1645172937699126000 == [IP |-> "192.168.1.100", AuthID |-> 99]
const_1645172937699127000 == [IP |-> "192.168.1.10", AuthID |-> 1]
const_1645172937699128000 == 20000
const_1645172937699129000 == [IP |-> "10.0.0.2", Port |-> 80]

\* ---------------- Abstract SPA / SDP attack model ----------------
MaxNonce == 1

VARIABLES net, fwRules, usedNonces, clientNonce, clientState,
          attackerKnown, svrAccessed, respondedTo

vars == <<net, fwRules, usedNonces, clientNonce, clientState,
          attackerKnown, svrAccessed, respondedTo>>

IPs   == {ClientCfg.IP, AttackerCfg.IP}
Ports == {USER_BASEPORT, ATTACKER_BASEPORT}

SPAUniverse ==
  [type : {"SPA"}, srcIP : IPs, srcPort : Ports,
   authID : {ClientCfg.AuthID, AttackerCfg.AuthID, UNKNOWN_AUTH_ID},
   nonce : 0..MaxNonce, hmac : BOOLEAN]

DataUniverse ==
  [type : {"DATA"}, srcIP : IPs, srcPort : Ports,
   dstIP : {SvrCfg.IP}, dstPort : {SvrCfg.Port}]

ClientRule == [srcIP |-> ClientCfg.IP, srcPort |-> MATCH_ANY,
               dstIP |-> SvrCfg.IP, dstPort |-> SvrCfg.Port]

ClientHasRule == \E r \in fwRules : r.srcIP = ClientCfg.IP

Init ==
  /\ net = {}
  /\ fwRules = {}
  /\ usedNonces = {}
  /\ clientNonce = 0
  /\ clientState = "init"
  /\ attackerKnown = {}
  /\ svrAccessed = {}
  /\ respondedTo = {}

\* Legitimate client sends an authenticated SPA knock to the SDP server
ClientSendSPA ==
  /\ clientState = "init"
  /\ clientNonce < MaxNonce
  /\ clientNonce' = clientNonce + 1
  /\ net' = net \cup {[type |-> "SPA", srcIP |-> ClientCfg.IP,
                       srcPort |-> USER_BASEPORT, authID |-> ClientCfg.AuthID,
                       nonce |-> clientNonce + 1, hmac |-> TRUE]}
  /\ clientState' = "spa_sent"
  /\ UNCHANGED <<fwRules, usedNonces, attackerKnown, svrAccessed, respondedTo>>

\* Client accesses the protected server once its rule has been opened
ClientSendData ==
  /\ clientState = "spa_sent"
  /\ ClientHasRule
  /\ net' = net \cup {[type |-> "DATA", srcIP |-> ClientCfg.IP,
                       srcPort |-> USER_BASEPORT, dstIP |-> SvrCfg.IP,
                       dstPort |-> SvrCfg.Port]}
  /\ clientState' = "data_sent"
  /\ UNCHANGED <<fwRules, usedNonces, clientNonce, attackerKnown,
                 svrAccessed, respondedTo>>

\* Attacker sniffs SPA packets on the wire
AttackerSniff ==
  /\ \E p \in net : p.type = "SPA" /\ p \notin attackerKnown
  /\ attackerKnown' = attackerKnown \cup {p \in net : p.type = "SPA"}
  /\ UNCHANGED <<net, fwRules, usedNonces, clientNonce, clientState,
                 svrAccessed, respondedTo>>

\* Attacker replays a sniffed SPA packet from its own address
AttackerReplay ==
  /\ \E p \in attackerKnown :
       net' = net \cup {[p EXCEPT !.srcIP = AttackerCfg.IP,
                                  !.srcPort = ATTACKER_BASEPORT]}
  /\ UNCHANGED <<fwRules, usedNonces, clientNonce, clientState,
                 attackerKnown, svrAccessed, respondedTo>>

\* Attacker forges SPA packets (DoS / brute-force attempt)
AttackerForge ==
  /\ \E aid \in {AttackerCfg.AuthID, UNKNOWN_AUTH_ID} :
       net' = net \cup {[type |-> "SPA", srcIP |-> AttackerCfg.IP,
                         srcPort |-> ATTACKER_BASEPORT, authID |-> aid,
                         nonce |-> 0, hmac |-> FALSE]}
  /\ UNCHANGED <<fwRules, usedNonces, clientNonce, clientState,
                 attackerKnown, svrAccessed, respondedTo>>

\* Attacker tries to reach the protected server directly
AttackerDataAccess ==
  /\ net' = net \cup {[type |-> "DATA", srcIP |-> AttackerCfg.IP,
                       srcPort |-> ATTACKER_BASEPORT, dstIP |-> SvrCfg.IP,
                       dstPort |-> SvrCfg.Port]}
  /\ UNCHANGED <<fwRules, usedNonces, clientNonce, clientState,
                 attackerKnown, svrAccessed, respondedTo>>

ValidSPA(p) ==
  /\ p.hmac
  /\ p.authID # UNKNOWN_AUTH_ID
  /\ p.authID = ClientCfg.AuthID
  /\ p.nonce \notin usedNonces
  /\ p.nonce > 0
  /\ (NAT_FLAG \/ p.srcIP = ClientCfg.IP)

\* SDP server silently processes SPA packets
SDPRecvSPA(p) ==
  /\ p \in net
  /\ p.type = "SPA"
  /\ net' = net \ {p}
  /\ IF ValidSPA(p)
       THEN /\ fwRules' = fwRules \cup
                 {[srcIP |-> p.srcIP, srcPort |-> MATCH_ANY,
                   dstIP |-> SvrCfg.IP, dstPort |-> SvrCfg.Port]}
            /\ usedNonces' = usedNonces \cup {p.nonce}
            /\ respondedTo' = respondedTo \cup {p.srcIP}
       ELSE UNCHANGED <<fwRules, usedNonces, respondedTo>>
  /\ UNCHANGED <<clientNonce, clientState, attackerKnown, svrAccessed>>

RuleMatches(r, p) ==
  /\ r.srcIP = p.srcIP
  /\ (r.srcPort = MATCH_ANY \/ r.srcPort = p.srcPort)
  /\ r.dstIP = p.dstIP
  /\ (r.dstPort = MATCH_ANY \/ r.dstPort = p.dstPort)

\* Firewall in front of the server: default drop, allow only matching rules
FwProcessData(p) ==
  /\ p \in net
  /\ p.type = "DATA"
  /\ net' = net \ {p}
  /\ IF \E r \in fwRules : RuleMatches(r, p)
       THEN /\ svrAccessed' = svrAccessed \cup {p.srcIP}
            /\ respondedTo' = respondedTo \cup {p.srcIP}
            /\ clientState' = IF p.srcIP = ClientCfg.IP
                                THEN "connected" ELSE clientState
       ELSE UNCHANGED <<svrAccessed, respondedTo, clientState>>
  /\ UNCHANGED <<fwRules, usedNonces, clientNonce, attackerKnown>>

Next ==
  \/ ClientSendSPA
  \/ ClientSendData
  \/ AttackerSniff
  \/ AttackerReplay
  \/ AttackerForge
  \/ AttackerDataAccess
  \/ \E p \in net : SDPRecvSPA(p)
  \/ \E p \in net : FwProcessData(p)

Spec == Init /\ [][Next]_vars

FairSpec ==
  /\ Spec
  /\ WF_vars(ClientSendSPA)
  /\ WF_vars(ClientSendData)
  /\ \A p \in SPAUniverse : WF_vars(SDPRecvSPA(p))
  /\ \A p \in DataUniverse : WF_vars(FwProcessData(p))

\* ---------------- Properties ----------------
SPASafeLaw ==
  \A r \in fwRules : r.srcIP = ClientCfg.IP

DataAccessSafeLaw ==
  AttackerCfg.IP \notin svrAccessed

SPA_AvailableProperty ==
  (clientState = "spa_sent") ~> ClientHasRule

SPA_AntiDosProperty ==
  /\ usedNonces \subseteq 1..clientNonce
  /\ Cardinality(fwRules) <= clientNonce

UserAccessAvailProperty ==
  <>(clientState = "connected")

SvrHidenProperty ==
  \A ip \in respondedTo : ip = ClientCfg.IP

FwRuleConsistentProperty ==
  /\ \A r \in fwRules : r.dstIP = SvrCfg.IP /\ r.dstPort = SvrCfg.Port
  /\ Cardinality(fwRules) <= Cardinality(usedNonces)

FwCorrectProperty ==
  \A ip \in svrAccessed : \E r \in fwRules : r.srcIP = ip

=============================================================================