---------------------------- MODULE ClientServerQueues ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Clients,        \* fixed, finite set of clients
    OpTypes,        \* finite set of operation types
    MaxQueueLen,    \* maximum length of each per-client request queue
    MaxRequests     \* bound on total requests per client (for finite model checking)

ASSUME /\ IsFiniteSet(Clients) /\ Clients # {}
       /\ IsFiniteSet(OpTypes) /\ OpTypes # {}
       /\ MaxQueueLen \in Nat /\ MaxQueueLen >= 1
       /\ MaxRequests \in Nat /\ MaxRequests >= 1

VARIABLES
    queue,      \* queue[c]    : Seq of pending requests from client c (FIFO)
    inflight,   \* inflight[c] : Seq of length <= 1; request being processed for c
    replies,    \* replies[c]  : Seq of replies produced by the server for c
    issued,     \* issued[c]   : history of all requests issued by client c
    observed    \* observed[c] : number of replies client c has observed

vars == <<queue, inflight, replies, issued, observed>>

-----------------------------------------------------------------------------------
Request == [client : Clients, id : 1..MaxRequests, op : OpTypes]
Reply   == [client : Clients, id : 1..MaxRequests, op : OpTypes, result : OpTypes]

\* Abstract, deterministic service semantics (implementation-agnostic)
Apply(o) == o

MkReply(r) == [client |-> r.client, id |-> r.id, op |-> r.op, result |-> Apply(r.op)]
ReqOf(rp)  == [client |-> rp.client, id |-> rp.id, op |-> rp.op]

RepliedReqs(c) == [i \in 1..Len(replies[c]) |-> ReqOf(replies[c][i])]

Pending(c) == queue[c] # <<>> \/ inflight[c] # <<>>

-----------------------------------------------------------------------------------
Init ==
    /\ queue    = [c \in Clients |-> <<>>]
    /\ inflight = [c \in Clients |-> <<>>]
    /\ replies  = [c \in Clients |-> <<>>]
    /\ issued   = [c \in Clients |-> <<>>]
    /\ observed = [c \in Clients |-> 0]

\* Client c places a request of type o (only if queue capacity permits)
ClientRequest(c, o) ==
    /\ Len(queue[c]) < MaxQueueLen
    /\ Len(issued[c]) < MaxRequests
    /\ LET r == [client |-> c, id |-> Len(issued[c]) + 1, op |-> o]
       IN  /\ queue'  = [queue  EXCEPT ![c] = Append(@, r)]
           /\ issued' = [issued EXCEPT ![c] = Append(@, r)]
    /\ UNCHANGED <<inflight, replies, observed>>

\* Server dequeues the head request of client c (sequential per client)
ServerDequeue(c) ==
    /\ inflight[c] = <<>>
    /\ queue[c] # <<>>
    /\ inflight' = [inflight EXCEPT ![c] = <<Head(queue[c])>>]
    /\ queue'    = [queue    EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED <<replies, issued, observed>>

\* Server processes the in-flight request of client c and produces its reply
ServerProcess(c) ==
    /\ inflight[c] # <<>>
    /\ replies'  = [replies  EXCEPT ![c] = Append(@, MkReply(Head(inflight[c])))]
    /\ inflight' = [inflight EXCEPT ![c] = <<>>]
    /\ UNCHANGED <<queue, issued, observed>>

\* Client c observes the next reply produced for it
ClientObserve(c) ==
    /\ observed[c] < Len(replies[c])
    /\ observed' = [observed EXCEPT ![c] = @ + 1]
    /\ UNCHANGED <<queue, inflight, replies, issued>>

ServerStep(c) == ServerDequeue(c) \/ ServerProcess(c)

Next ==
    \/ \E c \in Clients, o \in OpTypes : ClientRequest(c, o)
    \/ \E c \in Clients : ServerDequeue(c)
    \/ \E c \in Clients : ServerProcess(c)
    \/ \E c \in Clients : ClientObserve(c)

\* Fairness only on server steps, as required by the liveness goals.
Fairness ==
    \A c \in Clients : /\ WF_vars(ServerDequeue(c))
                       /\ WF_vars(ServerProcess(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ queue    \in [Clients -> Seq(Request)]
    /\ inflight \in [Clients -> Seq(Request)]
    /\ replies  \in [Clients -> Seq(Reply)]
    /\ issued   \in [Clients -> Seq(Request)]
    /\ observed \in [Clients -> 0..MaxRequests]
    /\ \A c \in Clients : Len(inflight[c]) <= 1

\* Resource safety: queue lengths never exceed the declared maximum
QueueBound ==
    \A c \in Clients : Len(queue[c]) <= MaxQueueLen

\* No request is ever lost: every issued request is replied, in flight, or queued
NoLostRequests ==
    \A c \in Clients :
        issued[c] = RepliedReqs(c) \o inflight[c] \o queue[c]

\* Each reply corresponds to the same client and operation type as its request
ReplyMatchesRequest ==
    \A c \in Clients :
        /\ Len(replies[c]) <= Len(issued[c])
        /\ \A i \in 1..Len(replies[c]) :
              /\ replies[c][i].client = c
              /\ replies[c][i].id     = issued[c][i].id
              /\ replies[c][i].op     = issued[c][i].op
              /\ replies[c][i].result = Apply(issued[c][i].op)

\* Per-client FIFO ordering: replies produced in the order requests were enqueued
PerClientOrdering ==
    \A c \in Clients :
        /\ \A i \in 1..Len(replies[c]) : replies[c][i].id = i
        /\ \A i \in 1..Len(issued[c])  : issued[c][i].id = i
        /\ \A i, j \in 1..Len(queue[c]) : i < j => queue[c][i].id < queue[c][j].id

\* Clients only observe replies that were actually produced
ObservedOK ==
    \A c \in Clients : observed[c] <= Len(replies[c])

Safety ==
    /\ TypeOK
    /\ QueueBound
    /\ NoLostRequests
    /\ ReplyMatchesRequest
    /\ PerClientOrdering
    /\ ObservedOK

-----------------------------------------------------------------------------------
\* Liveness properties

\* Every enqueued request eventually receives a response
EventualResponse ==
    \A c \in Clients, i \in 1..MaxRequests :
        (Len(issued[c]) >= i) ~> (Len(replies[c]) >= i)

\* The server does not permanently stall while requests are pending
Progress ==
    \A c \in Clients, n \in 0..MaxRequests :
        (Pending(c) /\ Len(replies[c]) = n) ~> (Len(replies[c]) > n)

\* All pending work is eventually drained
EventuallyDrained ==
    \A c \in Clients : Pending(c) ~> ~Pending(c)

THEOREM Spec => []Safety
THEOREM Spec => EventualResponse /\ Progress /\ EventuallyDrained
===================================================================================