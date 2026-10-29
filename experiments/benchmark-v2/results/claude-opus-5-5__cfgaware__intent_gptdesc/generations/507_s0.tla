---------------------------- MODULE SessionIdService ----------------------------
(***************************************************************************)
(* A client/server session-establishment protocol. The server assigns      *)
(* unique, strictly increasing session ids. The network may lose,          *)
(* reorder and delay messages. Clients and the server may crash and        *)
(* recover. The server's id counter is kept in stable storage, so it       *)
(* survives crashes and ids are never reused.                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* Model parameters (defined here so the module binds without constants)
Clients == {"c1", "c2"}
MaxId   == 4

NoId == 0
Ids  == 1..MaxId

VARIABLES
    nextId,      \* server's persistent counter (last id issued)
    issued,      \* set of all ids ever issued (persistent)
    serverUp,    \* is the server running?
    cState,      \* client state: "idle", "waiting", "has", "crashed"
    cSid,        \* session id currently known by each client
    net,         \* in-flight messages (set => reordering, loss, duplication)
    issuedTo     \* history: id -> client it was issued to (NoClient if none)

vars == <<nextId, issued, serverUp, cState, cSid, net, issuedTo>>

NoClient == "none"

Msg(t, c, s, ok) == [type |-> t, client |-> c, sid |-> s, ok |-> ok]

Messages ==
    { Msg(t, c, s, ok) : t \in {"req", "resp", "op", "ack"},
                         c \in Clients,
                         s \in Ids \cup {NoId},
                         ok \in BOOLEAN }

TypeOK ==
    /\ nextId \in 0..MaxId
    /\ issued \subseteq Ids
    /\ serverUp \in BOOLEAN
    /\ cState \in [Clients -> {"idle", "waiting", "has", "crashed"}]
    /\ cSid \in [Clients -> Ids \cup {NoId}]
    /\ net \subseteq Messages
    /\ issuedTo \in [Ids -> Clients \cup {NoClient}]

Init ==
    /\ nextId = 0
    /\ issued = {}
    /\ serverUp = TRUE
    /\ cState = [c \in Clients |-> "idle"]
    /\ cSid = [c \in Clients |-> NoId]
    /\ net = {}
    /\ issuedTo = [i \in Ids |-> NoClient]

-----------------------------------------------------------------------------
(* Client actions *)

ClientRequest(c) ==
    /\ cState[c] = "idle"
    /\ cState' = [cState EXCEPT ![c] = "waiting"]
    /\ net' = net \cup {Msg("req", c, NoId, FALSE)}
    /\ UNCHANGED <<nextId, issued, serverUp, cSid, issuedTo>>

ClientRetry(c) ==
    /\ cState[c] = "waiting"
    /\ Msg("req", c, NoId, FALSE) \notin net
    /\ net' = net \cup {Msg("req", c, NoId, FALSE)}
    /\ UNCHANGED <<nextId, issued, serverUp, cState, cSid, issuedTo>>

ClientRecvResp(c) ==
    \E m \in net :
        /\ m.type = "resp" /\ m.client = c
        /\ cState[c] /= "crashed"
        /\ net' = net \ {m}
        /\ IF cState[c] = "waiting"
              THEN /\ cState' = [cState EXCEPT ![c] = "has"]
                   /\ cSid' = [cSid EXCEPT ![c] = m.sid]
              ELSE UNCHANGED <<cState, cSid>>   \* stale/duplicate response
        /\ UNCHANGED <<nextId, issued, serverUp, issuedTo>>

ClientSendOp(c) ==
    /\ cState[c] = "has"
    /\ Msg("op", c, cSid[c], FALSE) \notin net
    /\ net' = net \cup {Msg("op", c, cSid[c], FALSE)}
    /\ UNCHANGED <<nextId, issued, serverUp, cState, cSid, issuedTo>>

ClientRecvAck(c) ==
    \E m \in net :
        /\ m.type = "ack" /\ m.client = c
        /\ net' = net \ {m}
        /\ UNCHANGED <<nextId, issued, serverUp, cState, cSid, issuedTo>>

ClientCrash(c) ==
    /\ cState[c] /= "crashed"
    /\ cState' = [cState EXCEPT ![c] = "crashed"]
    /\ cSid' = [cSid EXCEPT ![c] = NoId]
    /\ UNCHANGED <<nextId, issued, serverUp, net, issuedTo>>

ClientRecover(c) ==
    /\ cState[c] = "crashed"
    /\ cState' = [cState EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<nextId, issued, serverUp, cSid, net, issuedTo>>

-----------------------------------------------------------------------------
(* Server actions *)

ServerHandleReq(c) ==
    /\ serverUp
    /\ nextId < MaxId
    /\ Msg("req", c, NoId, FALSE) \in net
    /\ LET id == nextId + 1 IN
         /\ nextId' = id
         /\ issued' = issued \cup {id}
         /\ issuedTo' = [issuedTo EXCEPT ![id] = c]
         /\ net' = (net \ {Msg("req", c, NoId, FALSE)})
                     \cup {Msg("resp", c, id, FALSE)}
    /\ UNCHANGED <<serverUp, cState, cSid>>

ServerHandleOp ==
    /\ serverUp
    /\ \E m \in net :
         /\ m.type = "op"
         /\ net' = (net \ {m})
                     \cup {Msg("ack", m.client, m.sid, m.sid \in issued)}
    /\ UNCHANGED <<nextId, issued, serverUp, cState, cSid, issuedTo>>

ServerCrash ==
    /\ serverUp
    /\ serverUp' = FALSE
    /\ UNCHANGED <<nextId, issued, cState, cSid, net, issuedTo>>

\* nextId and issued are in stable storage and survive the crash
ServerRecover ==
    /\ ~serverUp
    /\ serverUp' = TRUE
    /\ UNCHANGED <<nextId, issued, cState, cSid, net, issuedTo>>

-----------------------------------------------------------------------------
(* Network faults *)

LoseMsg ==
    \E m \in net :
        /\ net' = net \ {m}
        /\ UNCHANGED <<nextId, issued, serverUp, cState, cSid, issuedTo>>

-----------------------------------------------------------------------------

Next ==
    \/ \E c \in Clients :
          \/ ClientRequest(c)
          \/ ClientRetry(c)
          \/ ClientRecvResp(c)
          \/ ClientSendOp(c)
          \/ ClientRecvAck(c)
          \/ ClientCrash(c)
          \/ ClientRecover(c)
          \/ ServerHandleReq(c)
    \/ ServerHandleOp
    \/ ServerCrash
    \/ ServerRecover
    \/ LoseMsg

(* Weak reliability: messages that are repeatedly available are eventually *)
(* delivered (strong fairness on receipt), retransmission is weakly fair,   *)
(* and a crashed server eventually recovers.                                *)
Fairness ==
    /\ \A c \in Clients :
          /\ WF_vars(ClientRequest(c))
          /\ WF_vars(ClientRetry(c))
          /\ SF_vars(ServerHandleReq(c))
          /\ SF_vars(ClientRecvResp(c))
    /\ WF_vars(ServerRecover)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Every id issued so far is exactly 1..nextId: ids are dense, unique, bounded
IssuedIsPrefix == issued = 1..nextId

\* Each issued id was given to exactly one client; unissued ids to none
UniqueIds ==
    \A i \in Ids : (i \in issued) <=> (issuedTo[i] /= NoClient)

\* No two clients hold the same session id
NoSharedSession ==
    \A c1, c2 \in Clients :
        (c1 /= c2 /\ cSid[c1] /= NoId) => cSid[c1] /= cSid[c2]

\* Any id a client holds or any id in a response was actually issued
HeldIdsIssued ==
    /\ \A c \in Clients : cSid[c] /= NoId => cSid[c] \in issued
    /\ \A m \in net : m.type = "resp" => m.sid \in issued

\* Positive acks only for issued ids
AcksSound ==
    \A m \in net : (m.type = "ack" /\ m.ok) => m.sid \in issued

Safety ==
    TypeOK /\ IssuedIsPrefix /\ UniqueIds /\ NoSharedSession
    /\ HeldIdsIssued /\ AcksSound

\* Counter never decreases; ids once issued are never revoked or reassigned
CounterMonotonic == [][nextId' >= nextId]_vars
IssuedStable == [][issued \subseteq issued']_vars
NoReuse ==
    [][\A i \in Ids : issuedTo[i] /= NoClient => issuedTo'[i] = issuedTo[i]]_vars
\* A newly issued id is strictly greater than every earlier issued id
NewIdGreater ==
    [][\A i \in issued' \ issued : \A j \in issued : i > j]_vars

(* Liveness: a waiting client that does not crash eventually gets an id,   *)
(* provided the server still has ids to hand out.                          *)
EventuallyGetsId ==
    \A c \in Clients :
        (cState[c] = "waiting" /\ nextId < MaxId)
            ~> (cState[c] \in {"has", "crashed"} \/ nextId = MaxId)

=============================================================================