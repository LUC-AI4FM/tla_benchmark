------------------------------- MODULE SessionIdService -------------------------------
(***************************************************************************)
(* A client/server session-establishment protocol. The server assigns      *)
(* unique, strictly increasing session ids. Clients and the server may     *)
(* crash and recover. The network may lose, reorder and duplicate messages *)
(* (retransmission). The server's id counter and its record of issued ids  *)
(* are kept on stable storage, so they survive server crashes. A client    *)
(* keeps only its request sequence number on stable storage. Its session   *)
(* id is volatile.                                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Clients,    \* set of client identifiers
    MaxId       \* bound used only by the TLC state constraint below

ASSUME MaxId \in Nat

VARIABLES
    counter,    \* server: last id issued (stable storage)
    issued,     \* server: set of <<client, id>> pairs ever issued (stable)
    serverUp,   \* server: TRUE iff server is running
    cState,     \* client: "idle" | "waiting" | "active" | "down"
    cSid,       \* client: session id currently held (0 = none)
    cRno,       \* client: current request number (stable storage)
    msgs,       \* network: set of in-flight messages (unordered, lossy)
    accepted,   \* server: set of <<client, id>> operations accepted
    rejected    \* server: set of <<client, id>> operations rejected

vars == <<counter, issued, serverUp, cState, cSid, cRno, msgs, accepted, rejected>>

NoId == 0
Ids  == Nat \ {0}

IssuedIds == { p[2] : p \in issued }

ReqMsg(c, n)     == [type |-> "req",  client |-> c, rno |-> n]
RespMsg(c, n, i) == [type |-> "resp", client |-> c, rno |-> n, sid |-> i]
OpMsg(c, i)      == [type |-> "op",   client |-> c, sid |-> i]

Messages ==
    [type : {"req"},  client : Clients, rno : Nat]
  \cup [type : {"resp"}, client : Clients, rno : Nat, sid : Ids]
  \cup [type : {"op"},   client : Clients, sid : Nat]

TypeOK ==
    /\ counter \in Nat
    /\ issued \subseteq (Clients \X Ids)
    /\ serverUp \in BOOLEAN
    /\ cState \in [Clients -> {"idle", "waiting", "active", "down"}]
    /\ cSid \in [Clients -> Nat]
    /\ cRno \in [Clients -> Nat]
    /\ msgs \subseteq Messages
    /\ accepted \subseteq (Clients \X Nat)
    /\ rejected \subseteq (Clients \X Nat)

Init ==
    /\ counter = 0
    /\ issued = {}
    /\ serverUp = TRUE
    /\ cState = [c \in Clients |-> "idle"]
    /\ cSid = [c \in Clients |-> NoId]
    /\ cRno = [c \in Clients |-> 0]
    /\ msgs = {}
    /\ accepted = {}
    /\ rejected = {}

(***************************************************************************)
(* Client actions                                                          *)
(***************************************************************************)

\* Client asks for a new session, using a fresh request number.
Request(c) ==
    /\ cState[c] = "idle"
    /\ cRno' = [cRno EXCEPT ![c] = cRno[c] + 1]
    /\ cState' = [cState EXCEPT ![c] = "waiting"]
    /\ msgs' = msgs \cup {ReqMsg(c, cRno[c] + 1)}
    /\ UNCHANGED <<counter, issued, serverUp, cSid, accepted, rejected>>

\* Client retransmits its current request. This tolerates loss.
Retransmit(c) ==
    /\ cState[c] = "waiting"
    /\ msgs' = msgs \cup {ReqMsg(c, cRno[c])}
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno, accepted, rejected>>

\* Client learns its session id from a response that matches its current request.
ClientRecvResp(c) ==
    /\ cState[c] = "waiting"
    /\ \E m \in msgs :
         /\ m.type = "resp"
         /\ m.client = c
         /\ m.rno = cRno[c]
         /\ cSid' = [cSid EXCEPT ![c] = m.sid]
         /\ cState' = [cState EXCEPT ![c] = "active"]
         /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<counter, issued, serverUp, cRno, accepted, rejected>>

\* Client discards a stale or unexpected response.
ClientDiscardResp(c) ==
    /\ cState[c] # "down"
    /\ \E m \in msgs :
         /\ m.type = "resp"
         /\ m.client = c
         /\ ~(cState[c] = "waiting" /\ m.rno = cRno[c])
         /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno, accepted, rejected>>

\* Client performs an operation that refers to its session id.
SendOp(c) ==
    /\ cState[c] = "active"
    /\ msgs' = msgs \cup {OpMsg(c, cSid[c])}
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno, accepted, rejected>>

\* A buggy or stale client refers to an arbitrary id. The server must reject it
\* unless that id was issued.
SendArbitraryOp(c) ==
    /\ cState[c] # "down"
    /\ \E i \in 1..(counter + 1) :
         msgs' = msgs \cup {OpMsg(c, i)}
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno, accepted, rejected>>

\* Client ends its session voluntarily.
EndSession(c) ==
    /\ cState[c] = "active"
    /\ cState' = [cState EXCEPT ![c] = "idle"]
    /\ cSid' = [cSid EXCEPT ![c] = NoId]
    /\ UNCHANGED <<counter, issued, serverUp, cRno, msgs, accepted, rejected>>

\* Client crashes and loses its volatile state. cRno is on stable storage.
ClientCrash(c) ==
    /\ cState[c] # "down"
    /\ cState' = [cState EXCEPT ![c] = "down"]
    /\ cSid' = [cSid EXCEPT ![c] = NoId]
    /\ UNCHANGED <<counter, issued, serverUp, cRno, msgs, accepted, rejected>>

ClientRecover(c) ==
    /\ cState[c] = "down"
    /\ cState' = [cState EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<counter, issued, serverUp, cSid, cRno, msgs, accepted, rejected>>

(***************************************************************************)
(* Server actions                                                          *)
(***************************************************************************)

\* Server handles a session request from client c and issues a brand-new id.
\* Every delivered request copy yields a fresh id. Ids are never reused.
ServerHandleReq(c) ==
    /\ serverUp
    /\ \E m \in msgs :
         /\ m.type = "req"
         /\ m.client = c
         /\ counter' = counter + 1
         /\ issued' = issued \cup {<<c, counter + 1>>}
         /\ msgs' = (msgs \ {m}) \cup {RespMsg(c, m.rno, counter + 1)}
    /\ UNCHANGED <<serverUp, cState, cSid, cRno, accepted, rejected>>

\* Server processes an operation. It accepts the operation only if the id was issued.
ServerHandleOp ==
    /\ serverUp
    /\ \E m \in msgs :
         /\ m.type = "op"
         /\ msgs' = msgs \ {m}
         /\ IF m.sid \in IssuedIds
              THEN /\ accepted' = accepted \cup {<<m.client, m.sid>>}
                   /\ UNCHANGED rejected
              ELSE /\ rejected' = rejected \cup {<<m.client, m.sid>>}
                   /\ UNCHANGED accepted
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno>>

\* Server crash. counter and issued are on stable storage and survive the crash.
ServerCrash ==
    /\ serverUp
    /\ serverUp' = FALSE
    /\ UNCHANGED <<counter, issued, cState, cSid, cRno, msgs, accepted, rejected>>

ServerRecover ==
    /\ ~serverUp
    /\ serverUp' = TRUE
    /\ UNCHANGED <<counter, issued, cState, cSid, cRno, msgs, accepted, rejected>>

(***************************************************************************)
(* Network: arbitrary message loss. Reordering is implicit in the set.     *)
(***************************************************************************)
LoseMsg ==
    /\ \E m \in msgs : msgs' = msgs \ {m}
    /\ UNCHANGED <<counter, issued, serverUp, cState, cSid, cRno, accepted, rejected>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
Next ==
    \/ \E c \in Clients :
         \/ Request(c)
         \/ Retransmit(c)
         \/ ClientRecvResp(c)
         \/ ClientDiscardResp(c)
         \/ SendOp(c)
         \/ SendArbitraryOp(c)
         \/ EndSession(c)
         \/ ClientCrash(c)
         \/ ClientRecover(c)
         \/ ServerHandleReq(c)
    \/ ServerHandleOp
    \/ ServerCrash
    \/ ServerRecover
    \/ LoseMsg

(***************************************************************************)
(* Fairness. These are the weak reliability assumptions.                   *)
(*  - A running client eventually issues and retransmits its request (WF). *)
(*  - A message that is repeatedly available is eventually delivered and   *)
(*    processed, despite intermittent loss and crashes (SF).               *)
(***************************************************************************)
Fairness ==
    \A c \in Clients :
        /\ WF_vars(Request(c))
        /\ WF_vars(Retransmit(c))
        /\ SF_vars(ServerHandleReq(c))
        /\ SF_vars(ClientRecvResp(c))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety: state invariants                                                *)
(***************************************************************************)

\* No id is ever assigned twice, to the same client or to different clients.
UniqueIds ==
    \A p, q \in issued : p[2] = q[2] => p = q

\* Issued ids are exactly 1..counter, so the counter reflects all issued ids.
CounterConsistent ==
    /\ \A p \in issued : p[2] \in 1..counter
    /\ \A i \in 1..counter : \E p \in issued : p[2] = i

\* A client holds only an id that the server issued to that client.
ClientSidIssued ==
    \A c \in Clients :
        cSid[c] # NoId => <<c, cSid[c]>> \in issued

\* No two clients observe the same session id.
DistinctClientSessions ==
    \A c1, c2 \in Clients :
        (c1 # c2 /\ cSid[c1] # NoId) => cSid[c1] # cSid[c2]

\* The server accepts an operation only if its id was previously issued.
OpsReferToIssuedIds ==
    \A p \in accepted : p[2] \in IssuedIds

\* All responses in flight carry issued ids.
ResponsesValid ==
    \A m \in msgs : m.type = "resp" => <<m.client, m.sid>> \in issued

Safety ==
    /\ TypeOK
    /\ UniqueIds
    /\ CounterConsistent
    /\ ClientSidIssued
    /\ DistinctClientSessions
    /\ OpsReferToIssuedIds
    /\ ResponsesValid

(***************************************************************************)
(* Safety: action properties                                               *)
(***************************************************************************)

\* The server's counter never decreases.
CounterMonotonic == [][counter' >= counter]_vars

\* Every newly issued id is strictly greater than all earlier issued ids.
NewIdsGreater ==
    [][\A p \in issued' \ issued : \A q \in issued : p[2] > q[2]]_vars

\* Ids are never withdrawn or reused, even across crashes.
NoReuse == [][issued \subseteq issued']_vars

(***************************************************************************)
(* Liveness                                                                *)
(* If client c and the server eventually stay up, then whenever c is       *)
(* waiting it eventually obtains a session id.                             *)
(***************************************************************************)
NonFaulty(c) == cState[c] # "down" /\ serverUp

EventuallyGetsSession ==
    \A c \in Clients :
        (<>[]NonFaulty(c)) =>
            [](cState[c] = "waiting" => <>(cState[c] = "active"))

\* A stably correct client obtains a session infinitely often.
EventuallyObtainsSession ==
    \A c \in Clients :
        (<>[]NonFaulty(c)) => []<>(cState[c] = "active")

(***************************************************************************)
(* State constraint for bounded model checking with TLC                    *)
(***************************************************************************)
StateConstraint ==
    /\ counter <= MaxId
    /\ \A c \in Clients : cRno[c] <= MaxId

THEOREM Spec => []Safety /\ CounterMonotonic /\ NewIdsGreater /\ NoReuse
THEOREM Spec => EventuallyGetsSession
=======================================================================================