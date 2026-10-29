```tla
ete a handshake using only data the attacker actually received.
AttackerAck ==
    /\ CanAttack
    /\ \E k \in aDataKnowledge :
         /\ k.type = "SYNACK"
         /\ chData' = chData \cup
              {DataPkt(pktId + 1, "ACK", ATTACKER_IP, k.dstPort,
                       SERVER_IP, SERVER_PORT, k.ack, k.seq)}
    /\ aSessions' = aSessions \cup
         {[type |-> "ack", authId |-> UNKNOWN_AUTH_ID, pid |-> pktId + 1]}
    /\ pktId' = pktId + 1
    /\ UNCHANGED <<aAuthKnowledge, aDataKnowledge, userVars, sdpVars, fwVars,
                   srvVars, chAuth, chCmd, chSrv, chReply>>

\* Receive packets addressed to the attacker's own IP.
AttackerRecv ==
    \E m \in chReply :
       /\ m.dstIp = ATTACKER_IP
       /\ chReply' = chReply \ {m}
       /\ aDataKnowledge' = aDataKnowledge \cup {m}
       /\ UNCHANGED <<aAuthKnowledge, aSessions, userVars, sdpVars, fwVars,
                      srvVars, chAuth, chCmd, chData, chSrv, pktId>>

AttackerNext ==
    \/ AttackerSniff \/ AttackerReplay \/ AttackerSpoof
    \/ AttackerScan \/ AttackerSpoofSyn \/ AttackerAck \/ AttackerRecv

-----------------------------------------------------------------------------
\* Stutter step once the system is quiescent, so the model does not deadlock.
Terminating ==
    /\ chAuth = {} /\ chCmd = {} /\ chData = {} /\ chSrv = {} /\ chReply = {}
    /\ UNCHANGED vars

Next ==
    \/ UserNext
    \/ SdpProcess
    \/ FwNext
    \/ ServerRecv
    \/ AttackerNext
    \/ Terminating

Fairness ==
    /\ WF_vars(UserRetransmit)
    /\ WF_vars(UserRecvSynAck)
    /\ WF_vars(UserDiscard)
    /\ WF_vars(SdpProcess)
    /\ WF_vars(FwApplyCmd)
    /\ WF_vars(FwFilter)
    /\ WF_vars(ServerRecv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* --------------------------- Safety properties ------------------------- *)

TypeOK ==
    /\ uState \in {"Idle", "Authenticating", "Connected"}
    /\ uTcpConns.state \in {"None", "SynSent", "Established"}
    /\ uRetrans \in 0..MAX_RETRANS
    /\ sdpReplayCnt \in Nat
    /\ sdpSpoofCnt \in Nat
    /\ pktId \in PktIds
    /\ uAuthSessions \subseteq PktIds
    /\ sdpProcessed \subseteq PktIds

\* The controller only accepts authIds the legitimate user actually issued.
OnlyLegitSessionsAccepted == sdpProcessed \subseteq uAuthSessions

\* The firewall never opens access for the attacker's IP.
NoAclForAttacker == \A r \in fwAcl : r.srcIp # ATTACKER_IP

\* Service hiding: the attacker never learns that the service exists.
ServiceHidden ==
    /\ \A i \in sServiceInfo : i.ip # ATTACKER_IP
    /\ \A k \in aDataKnowledge : k.srcIp # SERVER_IP

\* The attacker never establishes a TCP connection with the server.
NoAttackerConnection ==
    \A c \in sTcpConns : c.state = "Established" => c.cip # ATTACKER_IP

\* Every established server connection belongs to the legitimate user.
EstablishedOnlyLegit ==
    \A c \in sTcpConns :
       c.state = "Established" =>
          /\ c.cip = ClientPubIp
          /\ c.cisn = uTcpConns.isn
          /\ c.sisn = uTcpConns.srvIsn

\* No attack session ever yields an accepted session of its own: spoofed
\* SPA packets never produce an ACL rule.
AttackSessionsIneffective ==
    \A s \in aSessions :
       s.type = "spoof" => ~\E r \in fwAcl : r.srcIp = ATTACKER_IP

\* The detection counters are bounded by the number of attack attempts.
DetectionCountersSound ==
    sdpSpoofCnt <= Cardinality({s \in aSessions : s.type = "spoof"})

SafetyInvariant ==
    /\ TypeOK
    /\ OnlyLegitSessionsAccepted
    /\ NoAclForAttacker
    /\ ServiceHidden
    /\ NoAttackerConnection
    /\ EstablishedOnlyLegit
    /\ AttackSessionsIneffective
    /\ DetectionCountersSound

(* -------------------------- Liveness properties ------------------------ *)

\* A user who starts authenticating eventually connects. Model bounds such
\* as MAX_PKT and MAX_RETRANS can prevent this.
UserEventuallyConnected == (uState = "Authenticating") ~> (uState = "Connected")

\* Every SPA packet sent is eventually handled by the controller.
AuthEventuallyProcessed == \A m \in PktIds :
    (\E a \in chAuth : a.pid = m) ~> ~(\E a \in chAuth : a.pid = m)

\* Every accepted session eventually results in an installed ACL rule.
AclEventuallyInstalled == \A id \in PktIds :
    (id \in sdpProcessed) ~> (\E r \in fwAcl : r.authId = id)

THEOREM Spec => []SafetyInvariant
=============================================================================
```