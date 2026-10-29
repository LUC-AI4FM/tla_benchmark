<intrusions, replaysDetected, spoofsDetected, probesDropped, staleRejected>>

vars == <<now, clientPC, clientSPA, genuine, ctrlChan, dataChan, knownMacs,
          sniffedTuples, usedTS, fwRules, halfOpen, connections, acceptLog,
          attackAttempts, intrusions, replaysDetected, spoofsDetected,
          probesDropped, staleRejected>>

-----------------------------------------------------------------------------
(* Domains *)

Parties    == {"client", "attacker"}
IPs        == {ClientIP, AttackerIP, ServerIP}
Ports      == {ClientPort, AttackerPort, ServerPort}
IDs        == {ClientID, AttackerID}
Times      == 0..MaxTime
Registered == {ClientID}                 \* identity store

Content == [src : IPs, sport : Ports, dst : {ServerIP}, dport : {ServerPort},
            id : IDs, ts : Times]
Mac     == [valid : BOOLEAN, over : Content]
Packet  == [body : Content, mac : Mac, inj : Parties]
Syn     == [src : IPs, sport : Ports, dst : {ServerIP}, dport : {ServerPort},
            author : Parties]
Tuple   == [src : IPs, sport : Ports]
Rule    == [src : IPs, sport : Ports, dst : {ServerIP}, dport : {ServerPort},
            expiry : Nat, used : BOOLEAN]

ClientContent(t) ==
    [src |-> ClientIP, sport |-> ClientPort, dst |-> ServerIP,
     dport |-> ServerPort, id |-> ClientID, ts |-> t]

(* Dolev-Yao HMAC check: the MAC must be valid, must cover exactly this   *)
(* body, and must have been produced by the key holder.                  *)
MacOK(p) == p.mac.valid /\ p.mac.over = p.body /\ p.mac.over \in genuine

Key(b) == [id |-> b.id, ts |-> b.ts]

Matches(r, s) ==
    /\ r.src = s.src /\ r.sport = s.sport
    /\ r.dst = s.dst /\ r.dport = s.dport

-----------------------------------------------------------------------------
Init ==
    /\ now = 0
    /\ clientPC = "idle"
    /\ clientSPA = ClientContent(0)
    /\ genuine = {}
    /\ ctrlChan = {}
    /\ dataChan = {}
    /\ knownMacs = {}
    /\ sniffedTuples = {}
    /\ usedTS = {}
    /\ fwRules = {}
    /\ halfOpen = {}
    /\ connections = {}
    /\ acceptLog = {}
    /\ attackAttempts = 0
    /\ intrusions = 0
    /\ replaysDetected = 0
    /\ spoofsDetected = 0
    /\ probesDropped = 0
    /\ staleRejected = 0

-----------------------------------------------------------------------------
(* Legitimate client *)

\* Send the coupled SPA+SYN packet. Its body carries the identity, the
\* timestamp, and the exact 4-tuple.
ClientSendSPA ==
    /\ clientPC = "idle"
    /\ LET b == ClientContent(now) IN
         /\ genuine' = genuine \cup {b}
         /\ ctrlChan' = ctrlChan \cup
               {[body |-> b, mac |-> [valid |-> TRUE, over |-> b],
                 inj |-> "client"]}
         /\ clientSPA' = b
    /\ clientPC' = "waiting"
    /\ UNCHANGED <<now, dataChan>>
    /\ UNCHANGED attackerVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

\* The SPA was consumed without effect (for example, it was stale).
\* No pending copy remains and no handshake exists, so the client retries.
ClientRetry ==
    /\ clientPC = "waiting"
    /\ ~\E p \in ctrlChan : p.body = clientSPA
    /\ ~\E h \in halfOpen : h.author = "client"
    /\ ~\E k \in connections : k.owner = "client"
    /\ clientPC' = "idle"
    /\ UNCHANGED <<now, clientSPA, genuine, ctrlChan, dataChan>>
    /\ UNCHANGED attackerVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

-----------------------------------------------------------------------------
(* SDP Controller (validates the SPA and drives the firewall) *)

CtrlRejectSpoof(p) ==
    /\ \/ ~MacOK(p)
       \/ p.body.id \notin Registered
    /\ spoofsDetected' = spoofsDetected + 1
    /\ UNCHANGED <<intrusions, replaysDetected, probesDropped, staleRejected>>
    /\ UNCHANGED gatewayVars

CtrlRejectReplay(p) ==
    /\ MacOK(p)
    /\ p.body.id \in Registered
    /\ Key(p.body) \in usedTS
    /\ replaysDetected' = replaysDetected + 1
    /\ UNCHANGED <<intrusions, spoofsDetected, probesDropped, staleRejected>>
    /\ UNCHANGED gatewayVars

CtrlRejectStale(p) ==
    /\ MacOK(p)
    /\ p.body.id \in Registered
    /\ Key(p.body) \notin usedTS
    /\ now > p.body.ts + Window
    /\ staleRejected' = staleRejected + 1
    /\ UNCHANGED <<intrusions, replaysDetected, spoofsDetected, probesDropped>>
    /\ UNCHANGED gatewayVars

\* Accept. In one atomic step (the coupling), the controller records the
\* timestamp, installs an exact 4-tuple rule that is already consumed, and
\* forwards the coupled SYN to the server.
CtrlAccept(p) ==
    /\ MacOK(p)
    /\ p.body.id \in Registered
    /\ Key(p.body) \notin usedTS
    /\ now <= p.body.ts + Window
    /\ usedTS' = usedTS \cup {Key(p.body)}
    /\ fwRules' = fwRules \cup
          {[src |-> p.body.src, sport |-> p.body.sport,
            dst |-> p.body.dst, dport |-> p.body.dport,
            expiry |-> now + RuleTTL, used |-> TRUE]}
    /\ halfOpen' = halfOpen \cup
          {[src |-> p.body.src, sport |-> p.body.sport,
            author |-> IF p.body \in genuine THEN "client" ELSE "attacker"]}
    /\ acceptLog' = acceptLog \cup {[body |-> p.body, inj |-> p.inj]}
    /\ UNCHANGED connections
    /\ UNCHANGED counterVars

ControllerProcess ==
    \E p \in ctrlChan :
        /\ ctrlChan' = ctrlChan \ {p}
        /\ \/ CtrlRejectSpoof(p)
           \/ CtrlRejectReplay(p)
           \/ CtrlRejectStale(p)
           \/ CtrlAccept(p)
        /\ UNCHANGED <<now, dataChan>>
        /\ UNCHANGED clientVars
        /\ UNCHANGED attackerVars

-----------------------------------------------------------------------------
(* Firewall: default deny for plain SYNs *)

\* A plain SYN passes only if an exact-tuple rule exists that is unused
\* and unexpired. Under the coupled protocol no such rule ever exists.
FirewallFilter ==
    \E s \in dataChan :
        /\ dataChan' = dataChan \ {s}
        /\ IF \E r \in fwRules : Matches(r, s) /\ ~r.used /\ r.expiry >= now
           THEN \E r \in fwRules :
                  /\ Matches(r, s) /\ ~r.used /\ r.expiry >= now
                  /\ fwRules' = (fwRules \ {r}) \cup {[r EXCEPT !.used = TRUE]}
                  /\ halfOpen' = halfOpen \cup
                       {[src |-> s.src, sport |-> s.sport, author |-> s.author]}
                  /\ UNCHANGED probesDropped
           ELSE /\ probesDropped' = probesDropped + 1
                /\ UNCHANGED <<fwRules, halfOpen>>
        /\ UNCHANGED <<now, ctrlChan, usedTS, connections, acceptLog>>
        /\ UNCHANGED <<intrusions, replaysDetected, spoofsDetected, staleRejected>>
        /\ UNCHANGED clientVars
        /\ UNCHANGED attackerVars

\* Age out rules that have expired, or that were used and whose handshake
\* has finished.
AgeOutRule ==
    \E r \in fwRules :
        /\ \/ r.expiry <= now
           \/ /\ r.used
              /\ ~\E h \in halfOpen : h.src = r.src /\ h.sport = r.sport
        /\ fwRules' = fwRules \ {r}
        /\ UNCHANGED <<now, ctrlChan, dataChan, usedTS, halfOpen, connections, acceptLog>>
        /\ UNCHANGED clientVars
        /\ UNCHANGED attackerVars
        /\ UNCHANGED counterVars

-----------------------------------------------------------------------------
(* Protected server: TCP handshake completion *)

\* The server's SYN-ACK goes to the tuple. Only the party that generated
\* the SYN can produce a matching ACK. A replayed client SYN therefore
\* completes for the client.
CompleteHandshake ==
    \E h \in halfOpen :
        /\ halfOpen' = halfOpen \ {h}
        /\ connections' = connections \cup
              {[src |-> h.src, sport |-> h.sport, owner |-> h.author]}
        /\ intrusions' = IF h.author = "attacker" THEN intrusions + 1
                                                  ELSE intrusions
        /\ clientPC' = IF h.author = "client" THEN "connected" ELSE clientPC
        /\ UNCHANGED <<now, clientSPA, genuine, ctrlChan, dataChan>>
        /\ UNCHANGED <<usedTS, fwRules, acceptLog>>
        /\ UNCHANGED <<replaysDetected, spoofsDetected, probesDropped, staleRejected>>
        /\ UNCHANGED attackerVars

-----------------------------------------------------------------------------
(* Attacker (Dolev-Yao) *)

\* Sniff an SPA on the control plane.
AttackerSniffCtrl ==
    \E p \in ctrlChan :
        /\ p.inj = "client"
        /\ p.mac \notin knownMacs
        /\ knownMacs' = knownMacs \cup {p.mac}
        /\ UNCHANGED <<now, ctrlChan, dataChan, sniffedTuples, attackAttempts>>
        /\ UNCHANGED clientVars
        /\ UNCHANGED gatewayVars
        /\ UNCHANGED counterVars

\* Sniff TCP handshake or connection tuples on the data plane.
AttackerSniffData ==
    /\ \/ \E h \in halfOpen :
            /\ [src |-> h.src, sport |-> h.sport] \notin sniffedTuples
            /\ sniffedTuples' = sniffedTuples \cup {[src |-> h.src, sport |-> h.sport]}
       \/ \E k \in connections :
            /\ [src |-> k.src, sport |-> k.sport] \notin sniffedTuples
            /\ sniffedTuples' = sniffedTuples \cup {[src |-> k.src, sport |-> k.sport]}
    /\ UNCHANGED <<now, ctrlChan, dataChan, knownMacs, attackAttempts>>
    /\ UNCHANGED clientVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

\* Replay a captured SPA verbatim.
AttackerReplay ==
    /\ attackAttempts < MaxAttacks
    /\ \E m \in knownMacs :
         ctrlChan' = ctrlChan \cup
            {[body |-> m.over, mac |-> m, inj |-> "attacker"]}
    /\ attackAttempts' = attackAttempts + 1
    /\ UNCHANGED <<now, dataChan, knownMacs, sniffedTuples>>
    /\ UNCHANGED clientVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

\* Spoof or tamper with an SPA. The attacker may claim any identity or
\* tuple, including the client's own tuple under the shared NAT IP. It may
\* attach a sniffed MAC or a fabricated one, but not a verbatim replay.
AttackerBodies ==
    [src : {AttackerIP, ClientIP}, sport : {AttackerPort, ClientPort},
     dst : {ServerIP}, dport : {ServerPort}, id : IDs,
     ts : {now} \cup {m.over.ts : m \in knownMacs}]

AttackerSpoof ==
    /\ attackAttempts < MaxAttacks
    /\ \E b \in AttackerBodies :
         \E m \in knownMacs \cup {[valid |-> FALSE, over |-> b]} :
            /\ ~(m.valid /\ m.over = b)
            /\ ctrlChan' = ctrlChan \cup {[body |-> b, mac |-> m, inj |-> "attacker"]}
    /\ attackAttempts' = attackAttempts + 1
    /\ UNCHANGED <<now, dataChan, knownMacs, sniffedTuples>>
    /\ UNCHANGED clientVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

\* Probe the hidden service with the attacker's own tuple, or race a
\* legitimate rule using a sniffed (spoofed) tuple.
AttackerSendSYN ==
    /\ attackAttempts < MaxAttacks
    /\ \E t \in {[src |-> AttackerIP, sport |-> AttackerPort]} \cup sniffedTuples :
         dataChan' = dataChan \cup
            {[src |-> t.src, sport |-> t.sport, dst |-> ServerIP,
              dport |-> ServerPort, author |-> "attacker"]}
    /\ attackAttempts' = attackAttempts + 1
    /\ UNCHANGED <<now, ctrlChan, knownMacs, sniffedTuples>>
    /\ UNCHANGED clientVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

-----------------------------------------------------------------------------
(* Time *)

Tick ==
    /\ now < MaxTime
    /\ now' = now + 1
    /\ UNCHANGED <<ctrlChan, dataChan>>
    /\ UNCHANGED clientVars
    /\ UNCHANGED attackerVars
    /\ UNCHANGED gatewayVars
    /\ UNCHANGED counterVars

\* Terminal stuttering once the client is connected and nothing is pending.
Done ==
    /\ clientPC = "connected"
    /\ ctrlChan = {}
    /\ dataChan = {}
    /\ halfOpen = {}
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ ClientSendSPA
    \/ ClientRetry
    \/ ControllerProcess
    \/ FirewallFilter
    \/ AgeOutRule
    \/ CompleteHandshake
    \/ AttackerSniffCtrl
    \/ AttackerSniffData
    \/ AttackerReplay
    \/ AttackerSpoof
    \/ AttackerSendSYN
    \/ Tick
    \/ Done

Fairness ==
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(ClientRetry)
    /\ WF_vars(ControllerProcess)
    /\ WF_vars(FirewallFilter)
    /\ WF_vars(CompleteHandshake)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ now \in Times
    /\ clientPC \in {"idle", "waiting", "connected"}
    /\ clientSPA \in Content
    /\ genuine \subseteq Content
    /\ ctrlChan \subseteq Packet
    /\ dataChan \subseteq Syn
    /\ knownMacs \subseteq Mac
    /\ sniffedTuples \subseteq Tuple
    /\ usedTS \subseteq [id : IDs, ts : Times]
    /\ fwRules \subseteq Rule
    /\ halfOpen \subseteq [src : IPs, sport : Ports, author : Parties]
    /\ connections \subseteq [src : IPs, sport : Ports, owner : Parties]
    /\ acceptLog \subseteq [body : Content, inj : Parties]
    /\ attackAttempts \in 0..MaxAttacks
    /\ intrusions \in Nat
    /\ replaysDetected \in Nat
    /\ spoofsDetected \in Nat
    /\ probesDropped \in Nat
    /\ staleRejected \in Nat

\* 1. Service hiding: the attacker never establishes a connection. This
\*    holds for its own tuple, including when it shares the client's NAT IP.
ServiceHiding ==
    /\ \A k \in connections : k.owner = "client"
    /\ \A k \in connections : ~(k.src = AttackerIP /\ k.sport = AttackerPort)

\* 2. Replay prevention: each (identity, timestamp) is accepted at most once.
ReplayPrevention ==
    \A a, b \in acceptLog :
        (a.body.id = b.body.id /\ a.body.ts = b.body.ts) => a = b

\* 3. Spoofing prevention: only genuine SPAs from registered identities
\*    are accepted.
SpoofPrevention ==
    \A a \in acceptLog : a.body \in genuine /\ a.body.id \in Registered

\* 4. No unauthorized access. Any attacker connection would be counted.
IntrusionTraceability ==
    (\E k \in connections : k.owner = "attacker") => intrusions > 0

NoUnauthorizedAccess == intrusions = 0 /\ IntrusionTraceability

\* Precise rules: every rule matches an accepted SPA's exact tuple. Under
\* the coupled protocol no unused (raceable) rule ever exists.
RulePrecision ==
    \A r \in fwRules :
        /\ r.used
        /\ \E a \in acceptLog :
              /\ a.body.src = r.src /\ a.body.sport = r.sport
              /\ a.body.dst = r.dst /\ a.body.dport = r.dport

\* Rules are always time-limited.
RulesTimeLimited ==
    \A r \in fwRules : r.expiry <= MaxTime + RuleTTL

SafetyInvariants ==
    /\ TypeOK
    /\ ServiceHiding
    /\ ReplayPrevention
    /\ SpoofPrevention
    /\ NoUnauthorizedAccess
    /\ RulePrecision
    /\ RulesTimeLimited

(* Liveness *)

\* 5. Legitimate access guarantee.
LegitimateAccess == <>(clientPC = "connected")

LegitimateAccessStable == [](clientPC = "connected" => [](clientPC = "connected"))

THEOREM Spec => []SafetyInvariants
THEOREM Spec => LegitimateAccess
=============================================================================
```