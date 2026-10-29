------------------------------- MODULE SDP -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    ClientCfg,          \* record: [IP, LoginID]
    AttackerCfg,        \* record: [IP]
    SDPSvrCfg,          \* record: [IP, Port]
    SvrCfg,             \* record: [IP, Port]
    Key,                \* pre-shared SPA key of the legitimate client
    MATCH_ANY,          \* wildcard in firewall ACL rules
    NAT_FLAG,           \* TRUE if the client sits behind a NAT (port translation)
    UNKNOWN_AUTH_ID,    \* authentication id produced when decryption fails
    USER_BASEPORT,      \* base source port of the legitimate client
    ATTACKER_BASEPORT   \* base source port of the attacker

VARIABLES
    clientState,   \* "Init", "SPASent", "Authed", "SynSent", "Connected"
    net,           \* messages in flight on the public network
    log,           \* every message ever sent (Dolev-Yao eavesdropping)
    svrIn,         \* packets that passed the firewall and await the server
    passed,        \* history of packets the firewall let through
    fwRules,       \* firewall ACL rules (exact 4-tuples)
    authSessions,  \* SPA sessions accepted by the SDP controller
    usedNonces,    \* anti-replay store of the controller
    svrConns,      \* server side TCP connections
    attackCnt,     \* bound on attacker actions
    retrans        \* client SYN retransmission counter

vars == << clientState, net, log, svrIn, passed, fwRules, authSessions,
           usedNonces, svrConns, attackCnt, retrans >>

MaxAttack  == 2
MaxRetrans == 1

Users == { ClientCfg.LoginID }

ClientSPAPort  == USER_BASEPORT
ClientDataPort == USER_BASEPORT + 1
\* source port as observed outside the client (translated if behind NAT)
ClientOuterDataPort == IF NAT_FLAG THEN USER_BASEPORT + 2 ELSE ClientDataPort

ClientNonce == 1
AttackerNonce == 2

NoData == [ id |-> UNKNOWN_AUTH_ID, key |-> << >>, nonce |-> 0,
            cip |-> MATCH_ANY, cport |-> 0, svip |-> MATCH_ANY, svport |-> 0 ]

Msg(t, si, sp, di, dp, d) ==
    [ type |-> t, sip |-> si, sport |-> sp, dip |-> di, dport |-> dp, data |-> d ]

\* SPA packet with encrypted client/server tuple information
ClientSPA ==
    Msg("SPA", ClientCfg.IP, ClientSPAPort, SDPSvrCfg.IP, SDPSvrCfg.Port,
        [ id |-> ClientCfg.LoginID, key |-> << Key >>, nonce |-> ClientNonce,
          cip |-> ClientCfg.IP, cport |-> ClientDataPort,
          svip |-> SvrCfg.IP, svport |-> SvrCfg.Port ])

ClientSYN ==
    Msg("SYN", ClientCfg.IP, ClientOuterDataPort, SvrCfg.IP, SvrCfg.Port, NoData)

Send(m) == /\ net' = net \cup {m}
           /\ log' = log \cup {m}

Match(r, p) ==
    /\ r.sip = p.sip
    /\ (r.sport = MATCH_ANY \/ r.sport = p.sport)
    /\ r.dip = p.dip
    /\ r.dport = p.dport

RuleOf(s) == [ sip |-> s.sip, sport |-> s.sport, dip |-> s.dip, dport |-> s.dport ]

Decrypt(m) == IF m.data.key = << Key >> THEN m.data.id ELSE UNKNOWN_AUTH_ID

---------------------------------------------------------------------------
Init ==
    /\ clientState = "Init"
    /\ net = {}
    /\ log = {}
    /\ svrIn = {}
    /\ passed = {}
    /\ fwRules = {}
    /\ authSessions = {}
    /\ usedNonces = {}
    /\ svrConns = {}
    /\ attackCnt = 0
    /\ retrans = 0

----------------------------- Client --------------------------------------
ClientSendSPA ==
    /\ clientState = "Init"
    /\ Send(ClientSPA)
    /\ clientState' = "SPASent"
    /\ UNCHANGED << svrIn, passed, fwRules, authSessions, usedNonces,
                    svrConns, attackCnt, retrans >>

ClientRecvAck ==
    /\ clientState = "SPASent"
    /\ \E m \in net :
         /\ m.type = "SPA_ACK"
         /\ m.dip = ClientCfg.IP
         /\ m.data.nonce = ClientNonce
         /\ net' = net \ {m}
    /\ clientState' = "Authed"
    /\ UNCHANGED << log, svrIn, passed, fwRules, authSessions, usedNonces,
                    svrConns, attackCnt, retrans >>

ClientSendSYN ==
    /\ clientState = "Authed"
    /\ Send(ClientSYN)
    /\ clientState' = "SynSent"
    /\ UNCHANGED << svrIn, passed, fwRules, authSessions, usedNonces,
                    svrConns, attackCnt, retrans >>

ClientRetransSYN ==
    /\ clientState = "SynSent"
    /\ retrans < MaxRetrans
    /\ Send(ClientSYN)
    /\ retrans' = retrans + 1
    /\ UNCHANGED << clientState, svrIn, passed, fwRules, authSessions,
                    usedNonces, svrConns, attackCnt >>

ClientRecvSYNACK ==
    /\ clientState = "SynSent"
    /\ \E m \in net :
         /\ m.type = "SYNACK"
         /\ m.dip = ClientCfg.IP
         /\ m.dport = ClientOuterDataPort
         /\ m.sip = SvrCfg.IP
         /\ net' = net \ {m}
    /\ clientState' = "Connected"
    /\ UNCHANGED << log, svrIn, passed, fwRules, authSessions, usedNonces,
                    svrConns, attackCnt, retrans >>

\* Client discards packets it cannot use (stale acks, unexpected SYNACKs)
ClientDiscard ==
    /\ \E m \in net :
         /\ m.dip = ClientCfg.IP
         /\ \/ (m.type = "SPA_ACK" /\ clientState # "SPASent")
            \/ (m.type = "SYNACK" /\ clientState # "SynSent")
            \/ (m.type \notin {"SPA_ACK", "SYNACK"})
         /\ net' = net \ {m}
    /\ UNCHANGED << clientState, log, svrIn, passed, fwRules, authSessions,
                    usedNonces, svrConns, attackCnt, retrans >>

----------------------------- SDP Controller ------------------------------
ControllerRecvSPA ==
    \E m \in net :
      /\ m.type = "SPA"
      /\ m.dip = SDPSvrCfg.IP
      /\ LET id == Decrypt(m)
             d  == m.data
             ok == /\ id # UNKNOWN_AUTH_ID
                   /\ id \in Users
                   /\ d.nonce \notin usedNonces
                   /\ d.cip = m.sip              \* anti-spoof binding
             sess == [ id |-> id, nonce |-> d.nonce, sip |-> m.sip,
                       sport |-> IF NAT_FLAG THEN MATCH_ANY ELSE d.cport,
                       dip |-> d.svip, dport |-> d.svport ]
             ack == Msg("SPA_ACK", SDPSvrCfg.IP, SDPSvrCfg.Port, m.sip, m.sport,
                        [ NoData EXCEPT !.nonce = d.nonce ])
         IN IF ok
            THEN /\ authSessions' = authSessions \cup {sess}
                 /\ usedNonces' = usedNonces \cup {d.nonce}
                 /\ fwRules' = fwRules \cup {RuleOf(sess)}
                 /\ net' = (net \ {m}) \cup {ack}
                 /\ log' = log \cup {ack}
            ELSE \* silently drop: the controller stays hidden
                 /\ net' = net \ {m}
                 /\ UNCHANGED << authSessions, usedNonces, fwRules, log >>
      /\ UNCHANGED << clientState, svrIn, passed, svrConns, attackCnt, retrans >>

----------------------------- Firewall ------------------------------------
FirewallProcess ==
    \E p \in net :
      /\ p.dip = SvrCfg.IP
      /\ net' = net \ {p}
      /\ IF \E r \in fwRules : Match(r, p)
         THEN /\ svrIn' = svrIn \cup {p}
              /\ passed' = passed \cup {p}
         ELSE UNCHANGED << svrIn, passed >>
      /\ UNCHANGED << clientState, log, fwRules, authSessions, usedNonces,
                      svrConns, attackCnt, retrans >>

----------------------------- Server --------------------------------------
ServerRecvSYN ==
    \E p \in svrIn :
      /\ svrIn' = svrIn \ {p}
      /\ IF p.type = "SYN"
         THEN /\ svrConns' = svrConns \cup {[sip |-> p.sip, sport |-> p.sport]}
              /\ Send(Msg("SYNACK", SvrCfg.IP, SvrCfg.Port, p.sip, p.sport, NoData))
         ELSE UNCHANGED << svrConns, net, log >>
      /\ UNCHANGED << clientState, passed, fwRules, authSessions, usedNonces,
                      attackCnt, retrans >>

----------------------------- Attacker ------------------------------------
AttackerStep(m) ==
    /\ attackCnt < MaxAttack
    /\ attackCnt' = attackCnt + 1
    /\ Send(m)
    /\ UNCHANGED << clientState, svrIn, passed, fwRules, authSessions,
                    usedNonces, svrConns, retrans >>

\* Replay any eavesdropped message verbatim
AttackerReplay ==
    \E m \in log : m \notin net /\ AttackerStep(m)

\* Replay a captured SPA payload from the attacker's own address
AttackerReplaySPAFromSelf ==
    \E m \in log :
      /\ m.type = "SPA"
      /\ AttackerStep([ m EXCEPT !.sip = AttackerCfg.IP,
                                 !.sport = ATTACKER_BASEPORT ])

\* Forge an SPA packet without knowing the key
AttackerForgeSPA ==
    \E id \in { UNKNOWN_AUTH_ID, ClientCfg.LoginID } :
      AttackerStep(
        Msg("SPA", AttackerCfg.IP, ATTACKER_BASEPORT, SDPSvrCfg.IP, SDPSvrCfg.Port,
            [ id |-> id, key |-> << >>, nonce |-> AttackerNonce,
              cip |-> AttackerCfg.IP, cport |-> ATTACKER_BASEPORT + 1,
              svip |-> SvrCfg.IP, svport |-> SvrCfg.Port ]))

\* Probe the hidden server directly
AttackerProbe ==
    AttackerStep(Msg("SYN", AttackerCfg.IP, ATTACKER_BASEPORT + 1,
                     SvrCfg.IP, SvrCfg.Port, NoData))

\* Spoof a SYN with the legitimate client's address
AttackerSpoofSYN ==
    \E sp \in { USER_BASEPORT + 1, USER_BASEPORT + 2 } :
      AttackerStep(Msg("SYN", ClientCfg.IP, sp, SvrCfg.IP, SvrCfg.Port, NoData))

AttackerNext ==
    \/ AttackerReplay
    \/ AttackerReplaySPAFromSelf
    \/ AttackerForgeSPA
    \/ AttackerProbe
    \/ AttackerSpoofSYN

---------------------------------------------------------------------------
Next ==
    \/ ClientSendSPA
    \/ ClientRecvAck
    \/ ClientSendSYN
    \/ ClientRetransSYN
    \/ ClientRecvSYNACK
    \/ ClientDiscard
    \/ ControllerRecvSPA
    \/ FirewallProcess
    \/ ServerRecvSYN
    \/ AttackerNext

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(ClientSendSPA)
    /\ WF_vars(ClientRecvAck)
    /\ WF_vars(ClientSendSYN)
    /\ WF_vars(ClientRecvSYNACK)
    /\ WF_vars(ControllerRecvSPA)
    /\ WF_vars(FirewallProcess)
    /\ WF_vars(ServerRecvSYN)

----------------------------- Properties ----------------------------------
ClientAuthed == \E s \in authSessions : s.id = ClientCfg.LoginID

\* Only legitimate users with the correct key, from their real address, are authenticated
SPASafeLaw ==
    [](\A s \in authSessions : s.id \in Users /\ s.sip = ClientCfg.IP)

\* Anti-replay / anti-spoof / no responses to attackers
SPA_AntiDosProperty ==
    [](/\ \A s1, s2 \in authSessions : s1.nonce = s2.nonce => s1 = s2
       /\ \A s \in authSessions : s.sip # AttackerCfg.IP
       /\ \A m \in log : m.type = "SPA_ACK" => m.dip # AttackerCfg.IP
       /\ Cardinality(authSessions) = Cardinality(usedNonces))

\* Legitimate client eventually authenticates
SPA_AvailableProperty == <>ClientAuthed

\* Legitimate client eventually reaches the server
UserAccessAvailProperty == <>(clientState = "Connected")

\* Every server-side connection is backed by an authenticated session
DataAccessSafeLaw ==
    [](\A c \in svrConns :
         /\ c.sip # AttackerCfg.IP
         /\ \E s \in authSessions :
               /\ s.sip = c.sip
               /\ (s.sport = MATCH_ANY \/ s.sport = c.sport))

\* The attacker never receives anything from the hidden server
SvrHidenProperty ==
    [](\A m \in log : (m.sip = SvrCfg.IP) => m.dip # AttackerCfg.IP)

\* Firewall rules correspond exactly to authenticated sessions
FwRuleConsistentProperty ==
    [](/\ fwRules = { RuleOf(s) : s \in authSessions }
       /\ \A r \in fwRules : r.dip = SvrCfg.IP /\ r.dport = SvrCfg.Port
       /\ \A r \in fwRules : r.sip = ClientCfg.IP)

\* Firewall lets through only packets matching a rule, even with retransmissions
FwCorrectProperty ==
    [](/\ \A p \in passed : \E r \in fwRules : Match(r, p)
       /\ \A p \in passed : p.sip # AttackerCfg.IP
       /\ Cardinality(fwRules) <= 1)

=============================================================================