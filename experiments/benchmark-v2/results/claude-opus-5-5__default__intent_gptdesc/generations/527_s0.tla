---------------------------- MODULE LossyRequestReply ----------------------------
(***************************************************************************)
(* A single client and a single server exchange requests and replies over *)
(* two FIFO channels. The channels may lose messages but never duplicate  *)
(* or reorder them.                                                        *)
(*                                                                         *)
(* Request identifiers increase monotonically from 1 to MaxId. The client *)
(* may retransmit its outstanding request, and a retransmission reuses the *)
(* same identifier. The server processes each new identifier once. For a  *)
(* duplicate of the last request it served, the server may either ignore  *)
(* it or resend the cached reply. Stale requests are discarded.           *)
(*                                                                         *)
(* Bounds for model checking: identifiers lie in 1..MaxId, and each       *)
(* channel holds at most MaxMsgs messages.                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxId,      \* number of distinct requests the client will issue
    MaxMsgs     \* capacity bound of each channel

ASSUME /\ MaxId \in Nat \ {0}
       /\ MaxMsgs \in Nat \ {0}

Ids == 1..MaxId

VARIABLES
    clientState,   \* "idle" or "waiting"
    curId,         \* identifier of the client's current (latest) request; 0 = none yet
    reqChan,       \* client -> server channel (sequence of ids)
    repChan,       \* server -> client channel (sequence of ids)
    servLast,      \* last identifier processed by the server (0 = none)
    pendingReply,  \* reply the server has to send (0 = none)
    sent,          \* history: ids of requests the client has actually sent
    accepted       \* history: ids of replies the client has accepted

vars == << clientState, curId, reqChan, repChan, servLast,
           pendingReply, sent, accepted >>

-----------------------------------------------------------------------------
\* Remove the i-th element of a sequence (used to model message loss).
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

TypeOK ==
    /\ clientState \in {"idle", "waiting"}
    /\ curId \in 0..MaxId
    /\ reqChan \in Seq(Ids) /\ Len(reqChan) <= MaxMsgs
    /\ repChan \in Seq(Ids) /\ Len(repChan) <= MaxMsgs
    /\ servLast \in 0..MaxId
    /\ pendingReply \in 0..MaxId
    /\ sent \subseteq Ids
    /\ accepted \subseteq Ids

-----------------------------------------------------------------------------
Init ==
    /\ clientState = "idle"
    /\ curId = 0
    /\ reqChan = << >>
    /\ repChan = << >>
    /\ servLast = 0
    /\ pendingReply = 0
    /\ sent = {}
    /\ accepted = {}

(***************************************************************************)
(* Client actions                                                         *)
(***************************************************************************)

\* Issue a fresh request with the next identifier. If the channel is full,
\* the message is treated as lost; retransmission will recover from this.
ClientIssue ==
    /\ clientState = "idle"
    /\ curId < MaxId
    /\ curId' = curId + 1
    /\ clientState' = "waiting"
    /\ reqChan' = IF Len(reqChan) < MaxMsgs
                     THEN Append(reqChan, curId + 1)
                     ELSE reqChan
    /\ sent' = sent \cup {curId + 1}
    /\ UNCHANGED << repChan, servLast, pendingReply, accepted >>

\* Retransmit the outstanding request after an arbitrary delay,
\* reusing the same identifier.
ClientRetransmit ==
    /\ clientState = "waiting"
    /\ Len(reqChan) < MaxMsgs
    /\ reqChan' = Append(reqChan, curId)
    /\ UNCHANGED << clientState, curId, repChan, servLast,
                    pendingReply, sent, accepted >>

\* Receive a reply. Accept it only if it matches the outstanding request;
\* otherwise discard it.
ClientRecv ==
    /\ repChan # << >>
    /\ LET r == Head(repChan) IN
         /\ repChan' = Tail(repChan)
         /\ IF clientState = "waiting" /\ r = curId
               THEN /\ accepted' = accepted \cup {r}
                    /\ clientState' = "idle"
               ELSE UNCHANGED << accepted, clientState >>
    /\ UNCHANGED << curId, reqChan, servLast, pendingReply, sent >>

(***************************************************************************)
(* Server actions                                                         *)
(***************************************************************************)

\* Receive a new request (id greater than any served so far) and process it.
ServerRecvNew ==
    /\ reqChan # << >>
    /\ pendingReply = 0
    /\ Head(reqChan) > servLast
    /\ servLast' = Head(reqChan)
    /\ pendingReply' = Head(reqChan)
    /\ reqChan' = Tail(reqChan)
    /\ UNCHANGED << clientState, curId, repChan, sent, accepted >>

\* Receive a duplicate of the last served request and resend the cached reply.
ServerRecvDupReply ==
    /\ reqChan # << >>
    /\ pendingReply = 0
    /\ Head(reqChan) = servLast
    /\ pendingReply' = servLast
    /\ reqChan' = Tail(reqChan)
    /\ UNCHANGED << clientState, curId, repChan, servLast, sent, accepted >>

\* Receive a duplicate of the last served request and ignore it.
ServerRecvDupIgnore ==
    /\ reqChan # << >>
    /\ Head(reqChan) = servLast
    /\ reqChan' = Tail(reqChan)
    /\ UNCHANGED << clientState, curId, repChan, servLast,
                    pendingReply, sent, accepted >>

\* Discard a stale request whose identifier is older than the last one served.
ServerDiscardStale ==
    /\ reqChan # << >>
    /\ Head(reqChan) < servLast
    /\ reqChan' = Tail(reqChan)
    /\ UNCHANGED << clientState, curId, repChan, servLast,
                    pendingReply, sent, accepted >>

\* Send the pending reply, which carries the same identifier as the request.
ServerSend ==
    /\ pendingReply # 0
    /\ Len(repChan) < MaxMsgs
    /\ repChan' = Append(repChan, pendingReply)
    /\ pendingReply' = 0
    /\ UNCHANGED << clientState, curId, reqChan, servLast, sent, accepted >>

(***************************************************************************)
(* Unreliable channels: nondeterministic loss of any in-transit message   *)
(***************************************************************************)
DropReq ==
    /\ \E i \in 1..Len(reqChan) : reqChan' = RemoveAt(reqChan, i)
    /\ UNCHANGED << clientState, curId, repChan, servLast,
                    pendingReply, sent, accepted >>

DropRep ==
    /\ \E i \in 1..Len(repChan) : repChan' = RemoveAt(repChan, i)
    /\ UNCHANGED << clientState, curId, reqChan, servLast,
                    pendingReply, sent, accepted >>

\* Terminal state: all requests have been answered. Stuttering here
\* avoids a spurious deadlock report.
Finished ==
    /\ clientState = "idle"
    /\ curId = MaxId
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ ClientIssue
    \/ ClientRetransmit
    \/ ClientRecv
    \/ ServerRecvNew
    \/ ServerRecvDupReply
    \/ ServerRecvDupIgnore
    \/ ServerDiscardStale
    \/ ServerSend
    \/ DropReq
    \/ DropRep
    \/ Finished

(***************************************************************************)
(* Fairness. Message loss has no fairness, so it may happen arbitrarily.  *)
(* Delivery and processing use weak fairness where enabledness is stable. *)
(* They use strong fairness where loss can repeatedly disable an action.  *)
(* Strong fairness on delivery means that a channel which offers a        *)
(* message infinitely often eventually delivers one.                      *)
(* No fairness is placed on ServerRecvDupIgnore, so the server may ignore *)
(* duplicates, but it cannot ignore them forever.                         *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(ClientIssue)
    /\ SF_vars(ClientRetransmit)
    /\ SF_vars(ClientRecv)
    /\ SF_vars(ServerRecvNew)
    /\ SF_vars(ServerRecvDupReply)
    /\ WF_vars(ServerDiscardStale)
    /\ SF_vars(ServerSend)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

\* Integrity: every accepted reply corresponds to a request actually sent.
Integrity == accepted \subseteq sent

\* Every reply in transit or pending carries the id of some sent request.
RepliesFromSentRequests ==
    /\ \A i \in 1..Len(repChan) : repChan[i] \in sent
    /\ pendingReply # 0 => pendingReply \in sent
    /\ servLast # 0 => servLast \in sent

\* Reply matching (state form). The outstanding request has not been
\* accepted yet, and every earlier request has been.
ReplyMatchingState ==
    /\ clientState = "waiting" => /\ curId \notin accepted
                                  /\ accepted = 1..(curId - 1)
    /\ clientState = "idle"    => accepted = 1..curId

\* Reply matching (action form). The client accepts a reply only if its
\* identifier equals the current outstanding request's identifier.
ReplyMatching ==
    [][ accepted' # accepted =>
          /\ clientState = "waiting"
          /\ accepted' \ accepted = {curId} ]_vars

\* Identifiers are monotonically increasing.
MonotonicIds == [][curId' >= curId /\ servLast' >= servLast]_vars

\* Channels stay within their bounds.
BoundedChannels == Len(reqChan) <= MaxMsgs /\ Len(repChan) <= MaxMsgs

SafetyInv ==
    /\ TypeOK
    /\ Integrity
    /\ RepliesFromSentRequests
    /\ ReplyMatchingState
    /\ BoundedChannels

(***************************************************************************)
(* Liveness properties                                                    *)
(***************************************************************************)

\* Eventual response under fair delivery: every request that was sent and
\* continues to be retransmitted eventually gets a matching reply, which
\* the client accepts.
EventualResponse == \A i \in Ids : (i \in sent) ~> (i \in accepted)

\* While waiting, the client eventually accepts the reply for its
\* current request.
WaitingLeadsToAccept ==
    \A i \in Ids : (clientState = "waiting" /\ curId = i) ~> (i \in accepted)

\* Absence of livelock: retransmission cannot cycle forever without
\* progress. The client leaves the waiting state infinitely often or stays
\* idle, and the protocol eventually completes every request.
NoLivelock == []<>(clientState = "idle")

Completion == <>[](clientState = "idle" /\ curId = MaxId /\ accepted = Ids)

=============================================================================