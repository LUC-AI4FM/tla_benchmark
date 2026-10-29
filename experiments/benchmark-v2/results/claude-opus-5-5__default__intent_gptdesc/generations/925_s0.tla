---------------------------- MODULE InnerFIFO ----------------------------
(***************************************************************************)
(* A parameterized bounded FIFO queue ("inner FIFO") accessed by a set of  *)
(* concurrent clients.  Each client nondeterministically issues ENQUEUE or *)
(* DEQUEUE requests.  The queue serves them under these rules:             *)
(*   - ENQUEUE succeeds and appends to the tail if the queue is not full.  *)
(*     If the queue is full, the request is rejected (BlockWhenFull =      *)
(*     FALSE) or stays blocked until space frees up (BlockWhenFull = TRUE).*)
(*   - DEQUEUE succeeds and returns the head if the queue is nonempty.     *)
(*     If the queue is empty, it returns an "empty" indication.            *)
(* Every enqueued message is tagged with a unique id, so duplication and   *)
(* loss can be detected even when payload values repeat.                   *)
(*                                                                         *)
(* The module can be instantiated many times, for example                  *)
(*   Q1 == INSTANCE InnerFIFO WITH Msg <- M, Capacity <- 3, ...            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Msg,            \* finite message domain
    Capacity,       \* maximum number of buffered messages (fixed per instance)
    Clients,        \* set of concurrent client identifiers
    BlockWhenFull   \* TRUE: enqueue blocks when full; FALSE: enqueue is rejected

ASSUME CapAssump    == Capacity \in Nat /\ Capacity >= 1
ASSUME MsgAssump    == IsFiniteSet(Msg) /\ Msg # {}
ASSUME ClientAssump == Clients # {}
ASSUME BlockAssump  == BlockWhenFull \in BOOLEAN

VARIABLES
    queue,    \* the FIFO buffer: a sequence of tagged items
    enqLog,   \* history of all successfully enqueued items, in order
    deqLog,   \* history of all delivered (dequeued) items, in order
    nextId,   \* next unique id to attach to an enqueued item
    op,       \* op[c] \in {"idle","enq","deq"}: client c's current request
    arg,      \* arg[c]: payload of a pending enqueue (<<m>>), or <<>>
    resp      \* resp[c]: response record [kind, item]; item is <<>> or <<it>>

vars == <<queue, enqLog, deqLog, nextId, op, arg, resp>>

Item       == [id : Nat, val : Msg]
RespKinds  == {"none", "ok", "full", "empty", "item"}
NoResp     == [kind |-> "none", item |-> <<>>]

IsSeqOf(s, S) == /\ s \in Seq(S)
IsPrefix(s, t) == /\ Len(s) <= Len(t)
                  /\ SubSeq(t, 1, Len(s)) = s
Ids(s) == { s[i].id : i \in 1..Len(s) }
NoDup(s) == \A i, j \in 1..Len(s) : i # j => s[i].id # s[j].id
Increasing(s) == \A i, j \in 1..Len(s) : i < j => s[i].id < s[j].id

(***************************************************************************)
(* Explicit enabling conditions of the queue operations.                   *)
(***************************************************************************)
IsFull  == Len(queue) >= Capacity
IsEmpty == queue = <<>>
CanEnqueue == ~IsFull     \* successful enqueue possible
CanDequeue == ~IsEmpty    \* successful dequeue possible

Pending(c)   == op[c] # "idle" /\ resp[c].kind = "none"
Responded(c) == op[c] # "idle" /\ resp[c].kind # "none"

TypeOK ==
    /\ IsSeqOf(queue, Item)
    /\ IsSeqOf(enqLog, Item)
    /\ IsSeqOf(deqLog, Item)
    /\ nextId \in Nat
    /\ op \in [Clients -> {"idle", "enq", "deq"}]
    /\ \A c \in Clients : arg[c] \in Seq(Msg) /\ Len(arg[c]) <= 1
    /\ \A c \in Clients : /\ resp[c].kind \in RespKinds
                          /\ IsSeqOf(resp[c].item, Item)
                          /\ Len(resp[c].item) <= 1

Init ==
    /\ queue  = <<>>
    /\ enqLog = <<>>
    /\ deqLog = <<>>
    /\ nextId = 1
    /\ op     = [c \in Clients |-> "idle"]
    /\ arg    = [c \in Clients |-> <<>>]
    /\ resp   = [c \in Clients |-> NoResp]

(***************************************************************************)
(* Client actions: issuing requests and consuming responses.               *)
(***************************************************************************)
RequestEnq(c, m) ==
    /\ op[c] = "idle"
    /\ op'  = [op  EXCEPT ![c] = "enq"]
    /\ arg' = [arg EXCEPT ![c] = <<m>>]
    /\ UNCHANGED <<queue, enqLog, deqLog, nextId, resp>>

RequestDeq(c) ==
    /\ op[c] = "idle"
    /\ op'  = [op  EXCEPT ![c] = "deq"]
    /\ arg' = [arg EXCEPT ![c] = <<>>]
    /\ UNCHANGED <<queue, enqLog, deqLog, nextId, resp>>

Return(c) ==
    /\ Responded(c)
    /\ op'   = [op   EXCEPT ![c] = "idle"]
    /\ arg'  = [arg  EXCEPT ![c] = <<>>]
    /\ resp' = [resp EXCEPT ![c] = NoResp]
    /\ UNCHANGED <<queue, enqLog, deqLog, nextId>>

(***************************************************************************)
(* Queue actions that serve pending requests.                              *)
(***************************************************************************)
EnqOK(c) ==
    /\ Pending(c) /\ op[c] = "enq"
    /\ CanEnqueue
    /\ LET it == [id |-> nextId, val |-> Head(arg[c])]
       IN  /\ queue'  = Append(queue, it)
           /\ enqLog' = Append(enqLog, it)
    /\ nextId' = nextId + 1
    /\ resp'   = [resp EXCEPT ![c] = [kind |-> "ok", item |-> <<>>]]
    /\ UNCHANGED <<deqLog, op, arg>>

EnqReject(c) ==
    /\ ~BlockWhenFull
    /\ Pending(c) /\ op[c] = "enq"
    /\ IsFull
    /\ resp' = [resp EXCEPT ![c] = [kind |-> "full", item |-> <<>>]]
    /\ UNCHANGED <<queue, enqLog, deqLog, nextId, op, arg>>

DeqOK(c) ==
    /\ Pending(c) /\ op[c] = "deq"
    /\ CanDequeue
    /\ queue'  = Tail(queue)
    /\ deqLog' = Append(deqLog, Head(queue))
    /\ resp'   = [resp EXCEPT ![c] = [kind |-> "item", item |-> <<Head(queue)>>]]
    /\ UNCHANGED <<enqLog, nextId, op, arg>>

DeqEmpty(c) ==
    /\ Pending(c) /\ op[c] = "deq"
    /\ IsEmpty
    /\ resp' = [resp EXCEPT ![c] = [kind |-> "empty", item |-> <<>>]]
    /\ UNCHANGED <<queue, enqLog, deqLog, nextId, op, arg>>

ServeEnq(c) == EnqOK(c) \/ EnqReject(c)
ServeDeq(c) == DeqOK(c) \/ DeqEmpty(c)

Next ==
    \E c \in Clients :
        \/ \E m \in Msg : RequestEnq(c, m)
        \/ RequestDeq(c)
        \/ ServeEnq(c)
        \/ ServeDeq(c)
        \/ Return(c)

Fairness ==
    \A c \in Clients :
        /\ WF_vars(ServeEnq(c))
        /\ WF_vars(ServeDeq(c))
        /\ WF_vars(Return(c))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
CapacityBound == Len(queue) <= Capacity

\* Delivered messages are a prefix of enqueued messages.
DeliveredIsPrefix == IsPrefix(deqLog, enqLog)

\* No silent loss: every enqueued item is either delivered or still queued,
\* and the queue holds exactly the undelivered suffix, in order.
NoLoss == enqLog = deqLog \o queue

\* FIFO ordering: queue and delivery history are in enqueue order.
FIFOOrder == /\ Increasing(queue)
             /\ Increasing(deqLog)
             /\ Increasing(enqLog)

\* No duplicates anywhere, and no item is both delivered and still queued.
NoDuplicates == /\ NoDup(enqLog)
                /\ NoDup(deqLog)
                /\ NoDup(queue)
                /\ Ids(deqLog) \cap Ids(queue) = {}

\* Ids are fresh: every id ever issued is below nextId.
IdsFresh == \A i \in Ids(enqLog) : i < nextId

\* Responses are consistent with the enabling conditions.
ResponseConsistent ==
    \A c \in Clients :
        /\ resp[c].kind \in {"ok", "full"}   => op[c] = "enq"
        /\ resp[c].kind \in {"item", "empty"} => op[c] = "deq"
        /\ resp[c].kind = "full" => ~BlockWhenFull
        /\ resp[c].kind = "item" =>
              /\ Len(resp[c].item) = 1
              /\ \E i \in 1..Len(deqLog) : deqLog[i] = resp[c].item[1]

Safety ==
    /\ TypeOK
    /\ CapacityBound
    /\ DeliveredIsPrefix
    /\ NoLoss
    /\ FIFOOrder
    /\ NoDuplicates
    /\ IdsFresh
    /\ ResponseConsistent

(***************************************************************************)
(* Action-level safety properties.                                         *)
(***************************************************************************)
\* Histories only grow, so nothing is ever retracted or reordered.
HistoriesMonotone ==
    [][IsPrefix(enqLog, enqLog') /\ IsPrefix(deqLog, deqLog')]_vars

\* A dequeue always delivers exactly the current head.
DequeueTakesHead ==
    [][Len(deqLog') > Len(deqLog) =>
         /\ queue # <<>>
         /\ deqLog' = Append(deqLog, Head(queue))
         /\ queue' = Tail(queue)]_vars

\* An enqueue always appends at the tail and only when capacity permits.
EnqueueAtTail ==
    [][Len(enqLog') > Len(enqLog) =>
         /\ Len(queue) < Capacity
         /\ queue' = Append(queue, enqLog'[Len(enqLog')])]_vars

(***************************************************************************)
(* Liveness properties, which hold under the weak fairness in Spec.        *)
(***************************************************************************)
\* Every pending dequeue eventually gets an answer, either an item or "empty".
DeqEventuallyAnswered ==
    \A c \in Clients : (Pending(c) /\ op[c] = "deq") ~> Responded(c)

\* In reject mode, every pending enqueue eventually gets an answer.
\* In blocking mode, an enqueue that stays enabled eventually executes.
EnqEventuallyAnswered ==
    \A c \in Clients :
        IF BlockWhenFull
        THEN [](Pending(c) /\ op[c] = "enq" /\ CanEnqueue
                  => <>(~(Pending(c) /\ op[c] = "enq" /\ CanEnqueue)))
        ELSE (Pending(c) /\ op[c] = "enq") ~> Responded(c)

\* Every response is eventually consumed by its client.
ResponsesConsumed ==
    \A c \in Clients : Responded(c) ~> (op[c] = "idle")

Liveness == DeqEventuallyAnswered /\ EnqEventuallyAnswered /\ ResponsesConsumed

THEOREM Spec => []Safety
THEOREM Spec => HistoriesMonotone /\ DequeueTakesHead /\ EnqueueAtTail
THEOREM Spec => Liveness

(***************************************************************************)
(* Bound for finite model checking. Use as a TLC state CONSTRAINT and give *)
(* MaxEnqueues a value in the TLC model, e.g. MaxEnqueues == 4.            *)
(***************************************************************************)
StateConstraintFor(MaxEnqueues) == nextId <= MaxEnqueues + 1
=============================================================================