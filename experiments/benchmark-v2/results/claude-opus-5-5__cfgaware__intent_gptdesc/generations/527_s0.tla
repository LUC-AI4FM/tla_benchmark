---------------------------- MODULE ReliableRequestReply ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Bounds for model checking (defined as operators so that the fixed      *)
(* configuration only needs to bind Spec).                                 *)
(***************************************************************************)
MaxId   == 3          \* number of distinct request identifiers 1..MaxId
ChanCap == 2          \* capacity of each unreliable channel

Ids == 1..MaxId

VARIABLES
    clientId,      \* identifier of the client's current (latest) request; 0 = none yet
    cstate,        \* "idle" (may issue new request) or "waiting" (awaiting reply)
    reqChan,       \* client -> server channel (FIFO, lossy, no duplication)
    repChan,       \* server -> client channel (FIFO, lossy, no duplication)
    serverLast,    \* highest request id the server has processed
    sent,          \* history: set of request ids the client actually sent
    acceptedSet,   \* history: set of reply ids the client accepted
    lastAccepted   \* history: id of the most recently accepted reply

vars == << clientId, cstate, reqChan, repChan, serverLast,
           sent, acceptedSet, lastAccepted >>

Remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

TypeOK ==
    /\ clientId \in 0..MaxId
    /\ cstate \in {"idle", "waiting"}
    /\ reqChan \in Seq(Ids) /\ Len(reqChan) <= ChanCap
    /\ repChan \in Seq(Ids) /\ Len(repChan) <= ChanCap
    /\ serverLast \in 0..MaxId
    /\ sent \subseteq Ids
    /\ acceptedSet \subseteq Ids
    /\ lastAccepted \in 0..MaxId

Init ==
    /\ clientId = 0
    /\ cstate = "idle"
    /\ reqChan = << >>
    /\ repChan = << >>
    /\ serverLast = 0
    /\ sent = {}
    /\ acceptedSet = {}
    /\ lastAccepted = 0

(***************************************************************************)
(* Client actions                                                          *)
(***************************************************************************)
ClientSend ==
    /\ cstate = "idle"
    /\ clientId < MaxId
    /\ Len(reqChan) < ChanCap
    /\ clientId' = clientId + 1
    /\ cstate' = "waiting"
    /\ reqChan' = Append(reqChan, clientId + 1)
    /\ sent' = sent \cup {clientId + 1}
    /\ UNCHANGED << repChan, serverLast, acceptedSet, lastAccepted >>

\* Retransmission after an arbitrary delay reuses the same identifier.
ClientRetransmit ==
    /\ cstate = "waiting"
    /\ Len(reqChan) < ChanCap
    /\ reqChan' = Append(reqChan, clientId)
    /\ UNCHANGED << clientId, cstate, repChan, serverLast,
                    sent, acceptedSet, lastAccepted >>

ClientAccept ==
    /\ repChan /= << >>
    /\ cstate = "waiting"
    /\ Head(repChan) = clientId
    /\ repChan' = Tail(repChan)
    /\ cstate' = "idle"
    /\ acceptedSet' = acceptedSet \cup {Head(repChan)}
    /\ lastAccepted' = Head(repChan)
    /\ UNCHANGED << clientId, reqChan, serverLast, sent >>

ClientDiscard ==
    /\ repChan /= << >>
    /\ ~(cstate = "waiting" /\ Head(repChan) = clientId)
    /\ repChan' = Tail(repChan)
    /\ UNCHANGED << clientId, cstate, reqChan, serverLast,
                    sent, acceptedSet, lastAccepted >>

ClientRecv == ClientAccept \/ ClientDiscard

(***************************************************************************)
(* Server actions                                                          *)
(***************************************************************************)
\* Reply to a new request or (idempotently) to a duplicate of the latest one.
ServerReply ==
    /\ reqChan /= << >>
    /\ Head(reqChan) >= serverLast
    /\ reqChan' = Tail(reqChan)
    /\ serverLast' = Head(reqChan)
    /\ repChan' = IF Len(repChan) < ChanCap
                     THEN Append(repChan, Head(reqChan))
                     ELSE repChan          \* reply lost on full channel
    /\ UNCHANGED << clientId, cstate, sent, acceptedSet, lastAccepted >>

\* Stale duplicate requests may be ignored.
ServerIgnore ==
    /\ reqChan /= << >>
    /\ Head(reqChan) < serverLast
    /\ reqChan' = Tail(reqChan)
    /\ UNCHANGED << clientId, cstate, repChan, serverLast,
                    sent, acceptedSet, lastAccepted >>

ServerRecv == ServerReply \/ ServerIgnore

(***************************************************************************)
(* Unreliable channel: messages may be dropped (no duplication/reordering) *)
(***************************************************************************)
LoseReq ==
    /\ \E i \in 1..Len(reqChan) : reqChan' = Remove(reqChan, i)
    /\ UNCHANGED << clientId, cstate, repChan, serverLast,
                    sent, acceptedSet, lastAccepted >>

LoseRep ==
    /\ \E i \in 1..Len(repChan) : repChan' = Remove(repChan, i)
    /\ UNCHANGED << clientId, cstate, reqChan, serverLast,
                    sent, acceptedSet, lastAccepted >>

Lose == LoseReq \/ LoseRep

\* All identifiers used and answered: protocol complete.
Done ==
    /\ cstate = "idle"
    /\ clientId = MaxId
    /\ UNCHANGED vars

Next ==
    \/ ClientSend
    \/ ClientRetransmit
    \/ ClientRecv
    \/ ServerRecv
    \/ Lose
    \/ Done

(***************************************************************************)
(* Fairness: delivery/processing happens if enabled often enough.          *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(ClientSend)
    /\ WF_vars(ClientRetransmit)
    /\ SF_vars(ServerRecv)
    /\ SF_vars(ClientRecv)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Reply matching: an accepted reply always carries the current request id.
ReplyMatching ==
    (cstate = "idle" /\ clientId > 0) => lastAccepted = clientId

ReplyMatchingAction ==
    [][ClientAccept => Head(repChan) = clientId]_vars

\* Integrity: every accepted reply corresponds to a request actually sent.
Integrity ==
    /\ acceptedSet \subseteq sent
    /\ \A i \in 1..Len(repChan) : repChan[i] \in sent
    /\ \A i \in 1..Len(reqChan) : reqChan[i] \in sent

Safety == TypeOK /\ ReplyMatching /\ Integrity

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Every request that was sent (and retransmitted as needed) is eventually answered.
EventualResponse ==
    \A id \in Ids : (id \in sent) ~> (id \in acceptedSet)

\* No livelock: retransmission cannot cycle forever; the client keeps progressing
\* and the protocol eventually completes all requests.
NoLivelock ==
    (cstate = "waiting") ~> (cstate = "idle")

EventualCompletion ==
    <>[](cstate = "idle" /\ clientId = MaxId)

=============================================================================