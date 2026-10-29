ns its own key. The attacker only holds its own key. *)
Key(h)      == h
AttackerKey == Attacker

(* Abstract MAC: it can only be produced by a holder of key k, and it     *)
(* binds the client identity, the 4-tuple, the nonce and the timestamp.   *)
Mac(k, c, t, n, ts) == [key |-> k, client |-> c, tuple |-> t, nonce |-> n, ts |-> ts]

MacSpace == [key : Hosts, client : Clients, tuple : TupleSet,
             nonce : 1..MaxNonce, ts : 0..MaxTime]

SPAMsgs == [client : Clients, tuple : TupleSet, nonce : 1..MaxNonce,
            ts : 0..MaxTime, mac : MacSpace, via : {"client", "attacker"}]

Verdicts == {"accepted", "spoof", "replay", "outOfSync", "badTuple"}

TcpPkts == [origin : Hosts, tuple : TupleSet]

ClientStates == {"idle", "spaSent", "synSent", "connected"}

VARIABLES
    cstate,      \* client protocol state
    cnonce,      \* last nonce used by each client
    ctuple,      \* 4-tuple of each client's current session
    lastNonce,   \* controller: highest accepted nonce per client
    acl,         \* firewall: installed ephemeral ACL rules
    accepted,    \* controller: accepted (client, nonce) pairs
    ctrlLog,     \* controller: log of verdicts on SPA messages
    spaNet,      \* SPA messages in flight to the controller
    tcpNet,      \* TCP SYNs in flight to the firewall
    srvPending,  \* SYNs forwarded by the firewall to the server
    established, \* established TCP connections at the server
    fwLog,       \* firewall: log of dropped packets
    sniffed,     \* attacker: captured SPA messages
    sentSPA,     \* history: genuine SPA messages sent by clients
    now          \* global clock

clientVars == <<cstate, cnonce, ctuple>>
ctrlVars   == <<lastNonce, acl, accepted, ctrlLog>>
netVars    == <<spaNet, tcpNet, srvPending, established, fwLog>>
vars       == <<cstate, cnonce, ctuple, lastNonce, acl, accepted, ctrlLog,
                spaNet, tcpNet, srvPending, established, fwLog,
                sniffed, sentSPA, now>>

-----------------------------------------------------------------------------
(* Helper definitions *)

ValidMac(m) == m.mac = Mac(Key(m.client), m.client, m.tuple, m.nonce, m.ts)

Permitted(t) == \E r \in acl : r.tuple = t /\ r.expires > now

KnownTuples == {m.tuple : m \in sniffed} \cup {t \in TupleSet : t.src = Attacker}

-----------------------------------------------------------------------------
Init ==
    /\ cstate      = [c \in Clients |-> "idle"]
    /\ cnonce      = [c \in Clients |-> 0]
    /\ ctuple      = [c \in Clients |->
                        [src |-> c, sport |-> CHOOSE p \in SrcPorts : TRUE,
                         dst |-> Server, dport |-> ServicePort]]
    /\ lastNonce   = [c \in Clients |-> 0]
    /\ acl         = {}
    /\ accepted    = {}
    /\ ctrlLog     = {}
    /\ spaNet      = {}
    /\ tcpNet      = {}
    /\ srvPending  = {}
    /\ established = {}
    /\ fwLog       = {}
    /\ sniffed     = {}
    /\ sentSPA     = {}
    /\ now         = 0

-----------------------------------------------------------------------------
(* Client actions *)

ClientSendSPA(c, p) ==
    /\ cstate[c] = "idle"
    /\ cnonce[c] < MaxNonce
    /\ LET t == [src |-> c, sport |-> p, dst |-> Server, dport |-> ServicePort]
           n == cnonce[c] + 1
           m == [client |-> c, tuple |-> t, nonce |-> n, ts |-> now,
                 mac |-> Mac(Key(c), c, t, n, now), via |-> "client"]
       IN /\ spaNet'  = spaNet \cup {m}
          /\ sentSPA' = sentSPA \cup {m}
          /\ ctuple'  = [ctuple EXCEPT ![c] = t]
    /\ cnonce' = [cnonce EXCEPT ![c] = @ + 1]
    /\ cstate' = [cstate EXCEPT ![c] = "spaSent"]
    /\ UNCHANGED <<ctrlVars, tcpNet, srvPending, established, fwLog, sniffed, now>>

ClientSendSYN(c) ==
    /\ cstate[c] = "spaSent"
    /\ Permitted(ctuple[c])
    /\ tcpNet' = tcpNet \cup {[origin |-> c, tuple |-> ctuple[c]]}
    /\ cstate' = [cstate EXCEPT ![c] = "synSent"]
    /\ UNCHANGED <<cnonce, ctuple, ctrlVars, spaNet, srvPending, established,
                   fwLog, sniffed, sentSPA, now>>

ClientConnected(c) ==
    /\ cstate[c] = "synSent"
    /\ [tuple |-> ctuple[c], peer |-> c] \in established
    /\ cstate' = [cstate EXCEPT ![c] = "connected"]
    /\ UNCHANGED <<cnonce, ctuple, ctrlVars, netVars, sniffed, sentSPA, now>>

ClientClose(c) ==
    /\ cstate[c] = "connected"
    /\ established' = established \ {[tuple |-> ctuple[c], peer |-> c]}
    /\ cstate' = [cstate EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<cnonce, ctuple, ctrlVars, spaNet, tcpNet, srvPending, fwLog,
                   sniffed, sentSPA, now>>

-----------------------------------------------------------------------------
(* Controller actions *)

Reject(m, v) ==
    /\ ctrlLog' = ctrlLog \cup {[msg |-> m, verdict |-> v]}
    /\ UNCHANGED <<lastNonce, acl, accepted>>

Accept(m) ==
    /\ lastNonce' = [lastNonce EXCEPT ![m.client] = m.nonce]
    /\ acl' = acl \cup {[tuple |-> m.tuple, client |-> m.client,
                         nonce |-> m.nonce, expires |-> now + AclTTL]}
    /\ accepted' = accepted \cup {[client |-> m.client, nonce |-> m.nonce]}
    /\ ctrlLog' = ctrlLog \cup {[msg |-> m, verdict |-> "accepted"]}

ControllerProcess(m) ==
    /\ m \in spaNet
    /\ spaNet' = spaNet \ {m}
    /\ IF ~ValidMac(m)
         THEN Reject(m, "spoof")
       ELSE IF m.nonce <= lastNonce[m.client]
         THEN Reject(m, "replay")
       ELSE IF m.ts > now \/ now - m.ts > SpaWindow
         THEN Reject(m, "outOfSync")
       ELSE IF m.tuple.src # m.client \/ m.tuple.dst # Server
               \/ m.tuple.dport # ServicePort
         THEN Reject(m, "badTuple")
       ELSE Accept(m)
    /\ UNCHANGED <<clientVars, tcpNet, srvPending, established, fwLog,
                   sniffed, sentSPA, now>>

-----------------------------------------------------------------------------
(* Firewall and server actions *)

FirewallProcess(p) ==
    /\ p \in tcpNet
    /\ tcpNet' = tcpNet \ {p}
    /\ IF Permitted(p.tuple)
         THEN /\ srvPending' = srvPending \cup {p}
              /\ UNCHANGED fwLog
         ELSE /\ fwLog' = fwLog \cup {p}
              /\ UNCHANGED srvPending
    /\ UNCHANGED <<clientVars, ctrlVars, spaNet, established, sniffed,
                   sentSPA, now>>

(* The server's SYN-ACK goes to p.tuple.src. The handshake completes only *)
(* if the real initiator owns that address. Spoofed SYNs stay half-open   *)
(* and are discarded.                                                     *)
ServerProcess(p) ==
    /\ p \in srvPending
    /\ srvPending' = srvPending \ {p}
    /\ IF p.origin = p.tuple.src
         THEN established' = established \cup {[tuple |-> p.tuple, peer |-> p.origin]}
         ELSE UNCHANGED established
    /\ UNCHANGED <<clientVars, ctrlVars, spaNet, tcpNet, fwLog, sniffed,
                   sentSPA, now>>

-----------------------------------------------------------------------------
(* Attacker actions *)

AttackerSniff ==
    /\ \E m \in spaNet :
          /\ m \notin sniffed
          /\ sniffed' = sniffed \cup {m}
    /\ UNCHANGED <<clientVars, ctrlVars, netVars, sentSPA, now>>

AttackerReplay ==
    /\ \E m \in sniffed :
          LET r == [m EXCEPT !.via = "attacker"]
          IN /\ r \notin spaNet
             /\ spaNet' = spaNet \cup {r}
    /\ UNCHANGED <<clientVars, ctrlVars, tcpNet, srvPending, established,
                   fwLog, sniffed, sentSPA, now>>

AttackerTamper ==
    /\ \E m \in sniffed, t \in TupleSet :
          LET f == [m EXCEPT !.tuple = t, !.via = "attacker"]
          IN /\ f \notin spaNet
             /\ spaNet' = spaNet \cup {f}
    /\ UNCHANGED <<clientVars, ctrlVars, tcpNet, srvPending, established,
                   fwLog, sniffed, sentSPA, now>>

AttackerForge ==
    /\ \E c \in Clients, t \in TupleSet, n \in 1..MaxNonce :
          LET f == [client |-> c, tuple |-> t, nonce |-> n, ts |-> now,
                    mac |-> Mac(AttackerKey, c, t, n, now), via |-> "attacker"]
          IN /\ f \notin spaNet
             /\ spaNet' = spaNet \cup {f}
    /\ UNCHANGED <<clientVars, ctrlVars, tcpNet, srvPending, established,
                   fwLog, sniffed, sentSPA, now>>

AttackerProbe ==
    /\ \E t \in KnownTuples :
          LET p == [origin |-> Attacker, tuple |-> t]
          IN /\ p \notin tcpNet
             /\ tcpNet' = tcpNet \cup {p}
    /\ UNCHANGED <<clientVars, ctrlVars, spaNet, srvPending, established,
                   fwLog, sniffed, sentSPA, now>>

-----------------------------------------------------------------------------
(* Time and ACL expiry.                                                    *)
(* Bounded-delay assumption: time does not advance past the deadline of a *)
(* legitimate pending SPA or handshake. This means a legitimate handshake *)
(* completes within the SPA window and within the ACL lifetime.            *)

TickAllowed ==
    /\ now < MaxTime
    /\ \A c \in Clients :
          cstate[c] \in {"spaSent", "synSent"} =>
             \A r \in acl : r.tuple = ctuple[c] => r.expires > now + 1
    /\ \A m \in spaNet : m.via = "client" => now + 1 - m.ts <= SpaWindow

Tick ==
    /\ TickAllowed
    /\ now' = now + 1
    /\ acl' = {r \in acl : r.expires > now + 1}
    /\ UNCHANGED <<clientVars, lastNonce, accepted, ctrlLog, netVars,
                   sniffed, sentSPA>>

-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Clients, p \in SrcPorts : ClientSendSPA(c, p)
    \/ \E c \in Clients : ClientSendSYN(c) \/ ClientConnected(c) \/ ClientClose(c)
    \/ \E m \in spaNet : ControllerProcess(m)
    \/ \E p \in tcpNet : FirewallProcess(p)
    \/ \E p \in srvPending : ServerProcess(p)
    \/ AttackerSniff \/ AttackerReplay \/ AttackerTamper
    \/ AttackerForge \/ AttackerProbe
    \/ Tick

Fairness ==
    \A c \in Clients :
        /\ WF_vars(\E m \in spaNet : m.client = c /\ m.via = "client"
                                     /\ ControllerProcess(m))
        /\ WF_vars(ClientSendSYN(c))
        /\ WF_vars(\E p \in tcpNet : p.origin = c /\ FirewallProcess(p))
        /\ WF_vars(\E p \in srvPending : p.origin = c /\ ServerProcess(p))
        /\ WF_vars(ClientConnected(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ cstate \in [Clients -> ClientStates]
    /\ cnonce \in [Clients -> 0..MaxNonce]
    /\ ctuple \in [Clients -> TupleSet]
    /\ lastNonce \in [Clients -> 0..MaxNonce]
    /\ acl \subseteq [tuple : TupleSet, client : Clients, nonce : 1..MaxNonce,
                      expires : 0..(MaxTime + AclTTL)]
    /\ accepted \subseteq [client : Clients, nonce : 1..MaxNonce]
    /\ ctrlLog \subseteq [msg : SPAMsgs, verdict : Verdicts]
    /\ spaNet \subseteq SPAMsgs
    /\ sniffed \subseteq SPAMsgs
    /\ sentSPA \subseteq SPAMsgs
    /\ tcpNet \subseteq TcpPkts
    /\ srvPending \subseteq TcpPkts
    /\ fwLog \subseteq TcpPkts
    /\ established \subseteq [tuple : TupleSet, peer : Hosts]
    /\ now \in 0..MaxTime

(* An attacker without a client key never gets a connection to the server. *)
NoUnauthorizedConnection ==
    \A e \in established : e.peer \in Clients /\ e.tuple.src = e.peer

(* The firewall never forwards an attacker's own-source SYN to the server. *)
FirewallRejectsAttacker ==
    \A p \in srvPending : p.origin = Attacker => p.tuple.src # Attacker

(* Every ACL rule is tied to the authenticated 4-tuple of a genuine SPA. *)
ACLBoundToAuthenticatedTuple ==
    \A r \in acl :
        /\ r.client \in Clients
        /\ r.tuple.src = r.client
        /\ r.tuple.dst = Server /\ r.tuple.dport = ServicePort
        /\ [client |-> r.client, nonce |-> r.nonce] \in accepted
        /\ \E m \in sentSPA : /\ m.client = r.client
                              /\ m.nonce = r.nonce
                              /\ m.tuple = r.tuple

(* ACL rules are ephemeral: none outlives AclTTL. There is no permanent exposure. *)
ACLShortLived ==
    \A r \in acl : now < r.expires /\ r.expires <= now + AclTTL

(* Each (client, nonce) binding is accepted at most once. Replays never re-authorize. *)
NoReplayAcceptance ==
    \A e1, e2 \in ctrlLog :
        ( /\ e1.verdict = "accepted" /\ e2.verdict = "accepted"
          /\ e1.msg.client = e2.msg.client /\ e1.msg.nonce = e2.msg.nonce )
        => e1 = e2

(* Only genuine, unmodified client SPAs (or exact copies) are accepted. *)
ForgeryNeverAccepted ==
    \A e \in ctrlLog :
        e.verdict = "accepted" =>
            /\ ValidMac(e.msg)
            /\ [e.msg EXCEPT !.via = "client"] \in sentSPA

(* Spoofed or tampered SPAs are detected and logged as such. *)
SpoofsDetected ==
    \A e \in ctrlLog : ~ValidMac(e.msg) => e.verdict = "spoof"

(* Bounded-step guarantee: once a legitimate client sends its SYN, the     *)
(* matching ACL stays live until the handshake completes.                  *)
HandshakeWindowOpen ==
    \A c \in Clients : cstate[c] = "synSent" => Permitted(ctuple[c])

Safety ==
    /\ TypeOK
    /\ NoUnauthorizedConnection
    /\ FirewallRejectsAttacker
    /\ ACLBoundToAuthenticatedTuple
    /\ ACLShortLived
    /\ NoReplayAcceptance
    /\ ForgeryNeverAccepted
    /\ SpoofsDetected
    /\ HandshakeWindowOpen

-----------------------------------------------------------------------------
(* Liveness properties *)

(* A legitimate client that sends a fresh, valid SPA eventually connects. *)
LegitimateAccess ==
    \A c \in Clients : (cstate[c] = "spaSent") ~> (cstate[c] = "connected")

(* A valid SPA from a client is eventually processed by the controller. *)
ControllerResponds ==
    \A c \in Clients :
        (\E m \in spaNet : m.client = c /\ m.via = "client")
            ~> (\E r \in acl : r.tuple = ctuple[c]) \/ cstate[c] = "connected"

(* After the controller authorizes a valid SPA, the controller and firewall *)
(* together let the legitimate handshake complete.                          *)
ValidSPAPermitsHandshake ==
    \A c \in Clients :
        (cstate[c] \in {"spaSent", "synSent"} /\ Permitted(ctuple[c]))
            ~> ([tuple |-> ctuple[c], peer |-> c] \in established)

THEOREM Spec => []Safety
THEOREM Spec => LegitimateAccess /\ ControllerResponds /\ ValidSPAPermitsHandshake
=============================================================================