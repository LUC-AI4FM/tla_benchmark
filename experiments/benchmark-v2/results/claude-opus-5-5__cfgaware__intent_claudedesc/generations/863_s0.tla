------------------------------ MODULE SDP_SPA ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Key,
          MATCH_ANY,
          NAT_FLAG,
          UNKNOWN_AUTH_ID,
          USER_BASEPORT,
          ATTACKER_BASEPORT

-----------------------------------------------------------------------------
\* Static configuration of the participants
ClientCfg   == [authId |-> "alice", ip |-> "10.0.0.1"]
AttackerCfg == [ip |-> IF NAT_FLAG THEN ClientCfg.ip ELSE "10.0.0.66",
                forgedKey |-> "FORGED_KEY"]
SDPSvrCfg   == [ip |-> "10.0.1.1", port |-> 5000]
SvrCfg      == [ip |-> "10.0.2.1", port |-> 443]

MaxTime   == 3
RuleTTL   == 1
MaxAttack == 3

UserPorts     == {USER_BASEPORT, USER_BASEPORT + 1}
AttackerPorts == {ATTACKER_BASEPORT, ATTACKER_BASEPORT + 1}

\* Abstract (Dolev-Yao) HMAC: only computable by holders of the key
HMAC(k, authId, ts, sIp, sPort, dIp, dPort) ==
    <<k, authId, ts, sIp, sPort, dIp, dPort>>

MkSpa(authId, k, ts, sIp, sPort) ==
    [authId |-> authId, ts |-> ts,
     srcIp |-> sIp, srcPort |-> sPort,
     dstIp |-> SvrCfg.ip, dstPort |-> SvrCfg.port,
     hmac |-> HMAC(k, authId, ts, sIp, sPort, SvrCfg.ip, SvrCfg.port)]

ValidSig(m) ==
    m.hmac = HMAC(Key, m.authId, m.ts, m.srcIp, m.srcPort, m.dstIp, m.dstPort)

ValidCred(m) == m.authId = ClientCfg.authId

Tuple(p) == <<p.srcIp, p.srcPort, p.dstIp, p.dstPort>>

FMatch(rf, v) == rf = MATCH_ANY \/ rf = v

Match(r, p) == /\ FMatch(r.srcIp, p.srcIp)
               /\ FMatch(r.srcPort, p.srcPort)
               /\ FMatch(r.dstIp, p.dstIp)
               /\ FMatch(r.dstPort, p.dstPort)

-----------------------------------------------------------------------------
VARIABLES clock,            \* global time
          usedTs,           \* timestamps consumed by controller
          spaNet,           \* SPA messages in flight to controller
          accepted,         \* SPA messages accepted by controller
          fwRules,          \* firewall allow rules
          synNet,           \* SYN packets towards the firewall
          svrNet,           \* SYN packets forwarded to the server
          synAckNet,        \* SYN-ACK packets from the server
          forwarded,        \* tuples forwarded by the firewall
          svrConns,         \* connections established at server
          clientState,
          clientPort,
          clientSpa,
          atkSpa,           \* sniffed SPA messages
          atkTcp,           \* sniffed data-plane packets
          attackerConnected,
          attackCount,
          intrusionCount,
          replayRejects,
          spoofRejects

vars == <<clock, usedTs, spaNet, accepted, fwRules, synNet, svrNet, synAckNet,
          forwarded, svrConns, clientState, clientPort, clientSpa, atkSpa,
          atkTcp, attackerConnected, attackCount, intrusionCount,
          replayRejects, spoofRejects>>

NoMsg == [authId |-> "none"]

Init ==
    /\ clock = 0
    /\ usedTs = {}
    /\ spaNet = {}
    /\ accepted = {}
    /\ fwRules = {}
    /\ synNet = {}
    /\ svrNet = {}
    /\ synAckNet = {}
    /\ forwarded = {}
    /\ svrConns = {}
    /\ clientState = "init"
    /\ clientPort = USER_BASEPORT
    /\ clientSpa = NoMsg
    /\ atkSpa = {}
    /\ atkTcp = {}
    /\ attackerConnected = FALSE
    /\ attackCount = 0
    /\ intrusionCount = 0
    /\ replayRejects = 0
    /\ spoofRejects = 0

-----------------------------------------------------------------------------
\* Legitimate client: SPA packet coupled with its SYN (enhanced SPA)
ClientSendSPA ==
    /\ clientState = "init"
    /\ LET m   == MkSpa(ClientCfg.authId, Key, clock, ClientCfg.ip, clientPort)
           syn == [type |-> "SYN", srcIp |-> ClientCfg.ip, srcPort |-> clientPort,
                   dstIp |-> SvrCfg.ip, dstPort |-> SvrCfg.port]
       IN /\ spaNet' = spaNet \cup {m}
          /\ synNet' = synNet \cup {syn}
          /\ clientSpa' = m
    /\ clientState' = "syn_sent"
    /\ UNCHANGED <<clock, usedTs, accepted, fwRules, svrNet, synAckNet, forwarded,
                   svrConns, clientPort, atkSpa, atkTcp, attackerConnected,
                   attackCount, intrusionCount, replayRejects, spoofRejects>>

ClientRecvSynAck ==
    /\ clientState = "syn_sent"
    /\ \E a \in synAckNet :
         /\ a.dstIp = ClientCfg.ip
         /\ a.dstPort = clientPort
         /\ synAckNet' = synAckNet \ {a}
    /\ clientState' = "connected"
    /\ UNCHANGED <<clock, usedTs, spaNet, accepted, fwRules, synNet, svrNet,
                   forwarded, svrConns, clientPort, clientSpa, atkSpa, atkTcp,
                   attackerConnected, attackCount, intrusionCount,
                   replayRejects, spoofRejects>>

-----------------------------------------------------------------------------
\* SDP controller: verify HMAC, identity and timestamp freshness
CtrlProcessSpa ==
    \E m \in spaNet :
      /\ spaNet' = spaNet \ {m}
      /\ IF ValidSig(m) /\ ValidCred(m) /\ m.ts \notin usedTs
           THEN /\ usedTs' = usedTs \cup {m.ts}
                /\ accepted' = accepted \cup {m}
                /\ fwRules' = fwRules \cup
                     {[srcIp |-> m.srcIp, srcPort |-> m.srcPort,
                       dstIp |-> m.dstIp, dstPort |-> m.dstPort,
                       expire |-> clock + RuleTTL]}
                /\ UNCHANGED <<replayRejects, spoofRejects>>
         ELSE IF ValidSig(m) /\ ValidCred(m)
           THEN /\ replayRejects' = replayRejects + 1
                /\ UNCHANGED <<usedTs, accepted, fwRules, spoofRejects>>
           ELSE /\ spoofRejects' = spoofRejects + 1
                /\ UNCHANGED <<usedTs, accepted, fwRules, replayRejects>>
      /\ UNCHANGED <<clock, synNet, svrNet, synAckNet, forwarded, svrConns,
                     clientState, clientPort, clientSpa, atkSpa, atkTcp,
                     attackerConnected, attackCount, intrusionCount>>

-----------------------------------------------------------------------------
\* Firewall: default deny, exact tuple rules, consumed after use
PendingSpaFor(p) ==
    \E m \in spaNet : ValidSig(m) /\ ValidCred(m) /\ m.ts \notin usedTs
                      /\ Tuple(m) = Tuple(p)

FwForward ==
    \E p \in synNet, r \in fwRules :
      /\ Match(r, p)
      /\ synNet' = synNet \ {p}
      /\ fwRules' = fwRules \ {r}
      /\ svrNet' = svrNet \cup {p}
      /\ forwarded' = forwarded \cup {Tuple(p)}
      /\ UNCHANGED <<clock, usedTs, spaNet, accepted, synAckNet, svrConns,
                     clientState, clientPort, clientSpa, atkSpa, atkTcp,
                     attackerConnected, attackCount, intrusionCount,
                     replayRejects, spoofRejects>>

FwDrop ==
    \E p \in synNet :
      /\ ~\E r \in fwRules : Match(r, p)
      /\ ~PendingSpaFor(p)
      /\ synNet' = synNet \ {p}
      /\ UNCHANGED <<clock, usedTs, spaNet, accepted, fwRules, svrNet, synAckNet,
                     forwarded, svrConns, clientState, clientPort, clientSpa,
                     atkSpa, atkTcp, attackerConnected, attackCount,
                     intrusionCount, replayRejects, spoofRejects>>

FwAgeRule ==
    \E r \in fwRules :
      /\ clock > r.expire
      /\ ~\E p \in synNet : Match(r, p)
      /\ fwRules' = fwRules \ {r}
      /\ UNCHANGED <<clock, usedTs, spaNet, accepted, synNet, svrNet, synAckNet,
                     forwarded, svrConns, clientState, clientPort, clientSpa,
                     atkSpa, atkTcp, attackerConnected, attackCount,
                     intrusionCount, replayRejects, spoofRejects>>

Tick ==
    /\ clock < MaxTime
    /\ clock' = clock + 1
    /\ UNCHANGED <<usedTs, spaNet, accepted, fwRules, synNet, svrNet, synAckNet,
                   forwarded, svrConns, clientState, clientPort, clientSpa,
                   atkSpa, atkTcp, attackerConnected, attackCount,
                   intrusionCount, replayRejects, spoofRejects>>

-----------------------------------------------------------------------------
\* Protected server: answers SYNs that passed the firewall
SvrRecvSyn ==
    \E p \in svrNet :
      /\ svrNet' = svrNet \ {p}
      /\ synAckNet' = synAckNet \cup
           {[type |-> "SYNACK", srcIp |-> SvrCfg.ip, srcPort |-> SvrCfg.port,
             dstIp |-> p.srcIp, dstPort |-> p.srcPort]}
      /\ svrConns' = svrConns \cup {Tuple(p)}
      /\ UNCHANGED <<clock, usedTs, spaNet, accepted, fwRules, synNet, forwarded,
                     clientState, clientPort, clientSpa, atkSpa, atkTcp,
                     attackerConnected, attackCount, intrusionCount,
                     replayRejects, spoofRejects>>

-----------------------------------------------------------------------------
\* Attacker
AtkUnchangedExcept ==
    UNCHANGED <<clock, usedTs, accepted, fwRules, svrNet, forwarded, svrConns,
                clientState, clientPort, clientSpa, attackerConnected,
                intrusionCount, replayRejects, spoofRejects>>

AttackerSniffSpa ==
    \E m \in spaNet :
      /\ m \notin atkSpa
      /\ atkSpa' = atkSpa \cup {m}
      /\ UNCHANGED <<spaNet, synNet, synAckNet, atkTcp, attackCount>>
      /\ AtkUnchangedExcept

AttackerSniffTcp ==
    \E p \in synNet \cup synAckNet :
      /\ p \notin atkTcp
      /\ atkTcp' = atkTcp \cup {p}
      /\ UNCHANGED <<spaNet, synNet, synAckNet, atkSpa, attackCount>>
      /\ AtkUnchangedExcept

AttackerReplaySpa ==
    /\ attackCount < MaxAttack
    /\ \E m \in atkSpa :
         /\ spaNet' = spaNet \cup {m}
    /\ attackCount' = attackCount + 1
    /\ UNCHANGED <<synNet, synAckNet, atkSpa, atkTcp>>
    /\ AtkUnchangedExcept

\* Tamper a sniffed SPA so it would authorize the attacker's own tuple
AttackerTamperSpa ==
    /\ attackCount < MaxAttack
    /\ \E m \in atkSpa, port \in AttackerPorts :
         spaNet' = spaNet \cup
           {[m EXCEPT !.srcIp = AttackerCfg.ip, !.srcPort = port]}
    /\ attackCount' = attackCount + 1
    /\ UNCHANGED <<synNet, synAckNet, atkSpa, atkTcp>>
    /\ AtkUnchangedExcept

\* Forge an SPA with a key the attacker does not legitimately hold
AttackerForgeSpa ==
    /\ attackCount < MaxAttack
    /\ \E id \in {ClientCfg.authId, UNKNOWN_AUTH_ID}, port \in AttackerPorts :
         spaNet' = spaNet \cup
           {MkSpa(id, AttackerCfg.forgedKey, clock, AttackerCfg.ip, port)}
    /\ attackCount' = attackCount + 1
    /\ UNCHANGED <<synNet, synAckNet, atkSpa, atkTcp>>
    /\ AtkUnchangedExcept

\* Probe hidden service / race for rules opened for the legitimate user
AttackerSendSyn ==
    /\ attackCount < MaxAttack
    /\ \E port \in AttackerPorts :
         synNet' = synNet \cup
           {[type |-> "SYN", srcIp |-> AttackerCfg.ip, srcPort |-> port,
             dstIp |-> SvrCfg.ip, dstPort |-> SvrCfg.port]}
    /\ attackCount' = attackCount + 1
    /\ UNCHANGED <<spaNet, synAckNet, atkSpa, atkTcp>>
    /\ AtkUnchangedExcept

AttackerRecvSynAck ==
    \E a \in synAckNet :
      /\ a.dstIp = AttackerCfg.ip
      /\ a.dstPort \in AttackerPorts
      /\ synAckNet' = synAckNet \ {a}
      /\ attackerConnected' = TRUE
      /\ intrusionCount' = intrusionCount + 1
      /\ UNCHANGED <<clock, usedTs, spaNet, accepted, fwRules, synNet, svrNet,
                     forwarded, svrConns, clientState, clientPort, clientSpa,
                     atkSpa, atkTcp, attackCount, replayRejects, spoofRejects>>

AttackerNext ==
    \/ AttackerSniffSpa
    \/ AttackerSniffTcp
    \/ AttackerReplaySpa
    \/ AttackerTamperSpa
    \/ AttackerForgeSpa
    \/ AttackerSendSyn
    \/ AttackerRecvSynAck

Done ==
    /\ clientState = "connected"
    /\ UNCHANGED vars

Next ==
    \/ ClientSendSPA
    \/ ClientRecvSynAck
    \/ CtrlProcessSpa
    \/ FwForward
    \/ FwDrop
    \/ FwAgeRule
    \/ Tick
    \/ SvrRecvSyn
    \/ AttackerNext
    \/ Done

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(CtrlProcessSpa)
    /\ WF_vars(FwForward)
    /\ WF_vars(SvrRecvSyn)
    /\ WF_vars(ClientRecvSynAck)

-----------------------------------------------------------------------------
\* Safety properties

\* The hidden service is never reached by the attacker
SvrHidenProperty ==
    /\ ~attackerConnected
    /\ intrusionCount = 0

\* Only valid, fresh, authenticated SPA messages are accepted
SPASafeLaw ==
    /\ \A m \in accepted : ValidSig(m) /\ ValidCred(m)
    /\ \A m1, m2 \in accepted : m1.ts = m2.ts => m1 = m2

\* Rejected (replayed / spoofed) messages neither burn timestamps nor open rules
SPA_AntiDosProperty ==
    /\ usedTs = {m.ts : m \in accepted}
    /\ \A r \in fwRules : \E m \in accepted : Tuple(m) = Tuple(r)

\* Every server connection stems from an accepted SPA
DataAccessSafeLaw ==
    \A c \in svrConns : \E m \in accepted : Tuple(m) = c

\* Firewall only forwards traffic that was authorized
FwCorrectProperty ==
    \A t \in forwarded : \E m \in accepted : Tuple(m) = t

\* Firewall rules are exact-tuple and target only the protected service
FwRuleConsistentProperty ==
    \A r \in fwRules :
      /\ r.srcIp # MATCH_ANY
      /\ r.srcPort # MATCH_ANY
      /\ r.dstIp # MATCH_ANY
      /\ r.dstPort # MATCH_ANY
      /\ r.dstIp = SvrCfg.ip
      /\ r.dstPort = SvrCfg.port
      /\ r.srcPort \in UserPorts

\* Liveness properties
SPA_AvailableProperty ==
    (clientState = "syn_sent") ~>
        (\E m \in accepted : m.srcIp = ClientCfg.ip /\ m.srcPort = clientPort)

UserAccessAvailProperty ==
    <>(clientState = "connected")

=============================================================================