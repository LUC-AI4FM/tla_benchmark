------------------------------- MODULE ImprovedSDP -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    ClientIP,        \* IP address of the legitimate client
    AttackerIP,      \* IP address of the Dolev-Yao attacker
    ServerIP,        \* IP address of the hidden target server
    ServerPort,      \* service port of the hidden target server
    Ports,           \* set of possible client source ports
    MaxCounter,      \* bound on SPA anti-replay counter (number of sessions)
    MaxRetrans,      \* bound on TCP SYN retransmissions per session
    AttackBudget     \* bound on the number of attacker injections

ASSUME /\ ClientIP # AttackerIP
       /\ ClientIP # ServerIP
       /\ AttackerIP # ServerIP
       /\ Ports # {}
       /\ MaxCounter \in Nat \ {0}
       /\ MaxRetrans \in Nat
       /\ AttackBudget \in Nat

SrcIPs == {ClientIP, AttackerIP}

\* Exact 4-tuple describing a data-plane TCP connection attempt
TupleSet == [sip : SrcIPs, sport : Ports, dip : {ServerIP}, dport : {ServerPort}]

MkTuple(ip, p) == [sip |-> ip, sport |-> p, dip |-> ServerIP, dport |-> ServerPort]

NoTuple == "none"

\* SPA packet: the tuple and counter are inside the encrypted/HMAC-protected payload.
\* hmacOK = TRUE only for packets produced with the client's secret key.
SPAMsg == [src : SrcIPs, hmacOK : BOOLEAN, counter : 0..MaxCounter, tuple : TupleSet]

\* Data-plane TCP SYN packet; origin is a ghost field used only for verification
SynPkt == [tuple : TupleSet, origin : {"client", "attacker"}]

Session == [counter : 1..MaxCounter, tuple : TupleSet]

ClientStates == {"idle", "spaSent", "authenticated", "synSent", "connected"}

VARIABLES
    clientState,        \* legitimate client protocol state
    clientCounter,      \* client's monotonically increasing SPA counter
    clientTuple,        \* tuple bound to the client's current SPA session
    retrans,            \* SYN retransmissions in the current session
    net,                \* SPA packets in flight towards the controller
    observed,           \* SPA packets observed by the attacker (Dolev-Yao)
    ctrlLastCounter,    \* highest accepted SPA counter at the controller
    authSessions,       \* successfully authenticated SPA sessions
    authAck,            \* tuples for which the client got an authorization ack
    acl,                \* firewall exact 4-tuple ACL rules
    synQ,               \* SYN packets arriving at the firewall (FIFO)
    fwForwarded,        \* SYN packets forwarded by the firewall to the server
    fwDropped,          \* SYN packets silently dropped by the firewall
    attackerSawServer,  \* TRUE iff the attacker ever received a server response
    budget              \* remaining attacker injections

vars == <<clientState, clientCounter, clientTuple, retrans, net, observed,
          ctrlLastCounter, authSessions, authAck, acl, synQ, fwForwarded,
          fwDropped, attackerSawServer, budget>>

clientVars   == <<clientState, clientCounter, clientTuple, retrans>>
ctrlVars     == <<ctrlLastCounter, authSessions, authAck, acl>>
fwVars       == <<synQ, fwForwarded, fwDropped, attackerSawServer>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ clientState \in ClientStates
    /\ clientCounter \in 0..MaxCounter
    /\ clientTuple \in TupleSet \cup {NoTuple}
    /\ retrans \in 0..MaxRetrans
    /\ net \subseteq SPAMsg
    /\ observed \subseteq SPAMsg
    /\ ctrlLastCounter \in 0..MaxCounter
    /\ authSessions \subseteq Session
    /\ authAck \subseteq TupleSet
    /\ acl \subseteq TupleSet
    /\ synQ \in Seq(SynPkt)
    /\ fwForwarded \subseteq SynPkt
    /\ fwDropped \subseteq SynPkt
    /\ attackerSawServer \in BOOLEAN
    /\ budget \in 0..AttackBudget

Init ==
    /\ clientState = "idle"
    /\ clientCounter = 0
    /\ clientTuple = NoTuple
    /\ retrans = 0
    /\ net = {}
    /\ observed = {}
    /\ ctrlLastCounter = 0
    /\ authSessions = {}
    /\ authAck = {}
    /\ acl = {}
    /\ synQ = <<>>
    /\ fwForwarded = {}
    /\ fwDropped = {}
    /\ attackerSawServer = FALSE
    /\ budget = AttackBudget

-----------------------------------------------------------------------------
(* Legitimate client *)

\* Client sends an SPA binding a fresh counter to a concrete data-plane tuple
ClientSendSPA ==
    /\ clientState \in {"idle", "connected"}
    /\ clientCounter < MaxCounter
    /\ \E p \in Ports :
         LET t == MkTuple(ClientIP, p)
             m == [src |-> ClientIP, hmacOK |-> TRUE,
                   counter |-> clientCounter + 1, tuple |-> t]
         IN /\ clientTuple' = t
            /\ net' = net \cup {m}
            /\ observed' = observed \cup {m}   \* attacker sees all traffic
    /\ clientCounter' = clientCounter + 1
    /\ clientState' = "spaSent"
    /\ retrans' = 0
    /\ UNCHANGED <<ctrlVars, fwVars, budget>>

ClientAuthenticated ==
    /\ clientState = "spaSent"
    /\ clientTuple \in authAck
    /\ clientState' = "authenticated"
    /\ UNCHANGED <<clientCounter, clientTuple, retrans, net, observed,
                   ctrlVars, fwVars, budget>>

ClientSendSYN ==
    /\ clientState = "authenticated"
    /\ synQ' = Append(synQ, [tuple |-> clientTuple, origin |-> "client"])
    /\ clientState' = "synSent"
    /\ UNCHANGED <<clientCounter, clientTuple, retrans, net, observed,
                   ctrlVars, fwForwarded, fwDropped, attackerSawServer, budget>>

\* TCP SYN retransmission of the same exact 4-tuple
ClientRetransmit ==
    /\ clientState = "synSent"
    /\ retrans < MaxRetrans
    /\ synQ' = Append(synQ, [tuple |-> clientTuple, origin |-> "client"])
    /\ retrans' = retrans + 1
    /\ UNCHANGED <<clientState, clientCounter, clientTuple, net, observed,
                   ctrlVars, fwForwarded, fwDropped, attackerSawServer, budget>>

-----------------------------------------------------------------------------
(* SDP controller *)

ValidSPA(m) ==
    /\ m.hmacOK                       \* authentic (keyed HMAC verifies)
    /\ m.counter > ctrlLastCounter    \* anti-replay
    /\ m.src = m.tuple.sip            \* anti-spoof: source matches encrypted tuple

ControllerProcess ==
    \E m \in net :
        /\ net' = net \ {m}
        /\ IF ValidSPA(m)
              THEN /\ ctrlLastCounter' = m.counter
                   /\ authSessions' = authSessions \cup
                                       {[counter |-> m.counter, tuple |-> m.tuple]}
                   /\ acl' = acl \cup {m.tuple}       \* exact 4-tuple rule
                   /\ authAck' = authAck \cup {m.tuple}
              ELSE UNCHANGED ctrlVars                  \* silent discard
        /\ UNCHANGED <<clientVars, observed, fwVars, budget>>

-----------------------------------------------------------------------------
(* Firewall in front of the server *)

FirewallStep ==
    /\ synQ # <<>>
    /\ LET pkt == Head(synQ) IN
         /\ synQ' = Tail(synQ)
         /\ IF pkt.tuple \in acl
               THEN /\ fwForwarded' = fwForwarded \cup {pkt}
                    \* server replies SYN-ACK to pkt.tuple.sip
                    /\ attackerSawServer' = (attackerSawServer \/ pkt.tuple.sip = AttackerIP)
                    /\ fwDropped' = fwDropped
                    /\ IF clientState = "synSent" /\ pkt.tuple = clientTuple
                          THEN clientState' = "connected"
                          ELSE UNCHANGED clientState
               ELSE /\ fwDropped' = fwDropped \cup {pkt}   \* silent drop
                    /\ UNCHANGED <<fwForwarded, attackerSawServer, clientState>>
    /\ UNCHANGED <<clientCounter, clientTuple, retrans, net, observed,
                   ctrlVars, budget>>

-----------------------------------------------------------------------------
(* Dolev-Yao attacker *)

\* Replay of an observed SPA, possibly with a spoofed source address.
\* The encrypted payload (counter, tuple) cannot be altered without the key.
AttackerReplaySPA ==
    /\ budget > 0
    /\ \E m \in observed, s \in SrcIPs :
         net' = net \cup {[m EXCEPT !.src = s]}
    /\ budget' = budget - 1
    /\ UNCHANGED <<clientVars, observed, ctrlVars, fwVars>>

\* Forged SPA without the client key: HMAC does not verify
AttackerForgeSPA ==
    /\ budget > 0
    /\ \E s \in SrcIPs, c \in 0..MaxCounter, t \in TupleSet :
         net' = net \cup {[src |-> s, hmacOK |-> FALSE, counter |-> c, tuple |-> t]}
    /\ budget' = budget - 1
    /\ UNCHANGED <<clientVars, observed, ctrlVars, fwVars>>

\* Port probing / spoofed SYNs towards the server (any source IP, any port)
AttackerProbe ==
    /\ budget > 0
    /\ \E t \in TupleSet :
         synQ' = Append(synQ, [tuple |-> t, origin |-> "attacker"])
    /\ budget' = budget - 1
    /\ UNCHANGED <<clientVars, net, observed, ctrlVars,
                   fwForwarded, fwDropped, attackerSawServer>>

-----------------------------------------------------------------------------
Next ==
    \/ ClientSendSPA
    \/ ClientAuthenticated
    \/ ClientSendSYN
    \/ ClientRetransmit
    \/ ControllerProcess
    \/ FirewallStep
    \/ AttackerReplaySPA
    \/ AttackerForgeSPA
    \/ AttackerProbe

Fairness ==
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(ClientAuthenticated)
    /\ WF_vars(ClientSendSYN)
    /\ WF_vars(ControllerProcess)
    /\ WF_vars(FirewallStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* SPA authentication: every authenticated session originates from the legitimate client
SPAAuthentication ==
    \A s \in authSessions :
        /\ s.tuple.sip = ClientIP
        /\ s.counter \in 1..clientCounter

\* Anti-replay: each counter value is accepted at most once
AntiReplay ==
    /\ \A s1, s2 \in authSessions : s1.counter = s2.counter => s1 = s2
    /\ \A s \in authSessions : s.counter <= ctrlLastCounter
    /\ Cardinality(authSessions) <= clientCounter

\* Anti-spoof: no ACL rule or forwarded packet is bound to the attacker's address
AntiSpoof ==
    /\ \A t \in acl : t.sip = ClientIP
    /\ \A p \in fwForwarded : p.tuple.sip # AttackerIP

\* Server hiddenness: the attacker never receives any response from the server
ServerHidden == ~attackerSawServer

\* Firewall rule consistency: ACL rules are exactly the authenticated exact 4-tuples
FirewallRuleConsistency ==
    /\ acl = {s.tuple : s \in authSessions}
    /\ \A t \in acl : t.dip = ServerIP /\ t.dport = ServerPort
    /\ authAck \subseteq acl

\* Firewall correctness under retransmissions: no legitimate SYN (original or
\* retransmitted) is ever dropped, and only ACL-matching packets are forwarded
FirewallRetransCorrectness ==
    /\ \A p \in fwDropped : p.origin # "client"
    /\ \A p \in fwForwarded : p.tuple \in acl
    /\ retrans <= MaxRetrans

\* Client never connects without an authorized rule
ConnectedImpliesAuthorized ==
    clientState \in {"authenticated", "synSent", "connected"} => clientTuple \in acl

Safety ==
    /\ TypeOK
    /\ SPAAuthentication
    /\ AntiReplay
    /\ AntiSpoof
    /\ ServerHidden
    /\ FirewallRuleConsistency
    /\ FirewallRetransCorrectness
    /\ ConnectedImpliesAuthorized

\* ACL rules persist (needed so retransmissions keep matching)
ACLMonotonic == [][acl \subseteq acl']_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every SPA that is sent is eventually processed by the controller
SPAEventuallyProcessed == \A m \in SPAMsg : (m \in net) ~> (m \notin net)

\* A legitimate SPA eventually leads to authentication
SPAEventuallyAuthenticated == (clientState = "spaSent") ~> (clientState = "authenticated")

\* Legitimate user access availability
LegitAccess == (clientState = "spaSent") ~> (clientState = "connected")

\* Retransmission scenario: once SYNs are sent, the client eventually connects
RetransLiveness == (clientState = "synSent") ~> (clientState = "connected")

EventualAccess == <>(clientState = "connected")

\* Firewall eventually handles all queued packets
FirewallDrains == []<>(synQ = <<>>)

THEOREM Spec => []Safety
THEOREM Spec => ACLMonotonic
THEOREM Spec => (LegitAccess /\ RetransLiveness /\ EventualAccess)
==============================================================================