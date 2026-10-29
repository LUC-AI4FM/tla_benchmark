------------------------------ MODULE BoundedQueueService ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Clients,    \* fixed set of clients
    Values,     \* value domain
    N,          \* maximum capacity
    NoVal       \* neutral value, not in Values

ASSUME CapAssump    == N \in Nat /\ N >= 1
ASSUME NoValAssump  == NoVal \notin Values
ASSUME ClientAssump == Clients # {}

VARIABLES
    queue,      \* shared queue (sequence of values)
    ret,        \* ret[c] : per-client observable return record
    enqCnt,     \* ghost: number of successful enqueues of each value
    deqCnt      \* ghost: number of successful dequeues of each value

vars == <<queue, ret, enqCnt, deqCnt>>

----------------------------------------------------------------------------------------
(* Return records *)

Neutral == [op |-> "none", status |-> "none", val |-> NoVal]

RetSet ==
       {Neutral}
  \cup [op : {"enq"}, status : {"ok", "full"}, val : Values]
  \cup [op : {"deq"}, status : {"ok"}, val : Values]
  \cup [op : {"deq"}, status : {"empty"}, val : {NoVal}]

Count(s, v) == Cardinality({i \in 1..Len(s) : s[i] = v})

----------------------------------------------------------------------------------------
TypeOK ==
    /\ queue \in Seq(Values)
    /\ ret \in [Clients -> RetSet]
    /\ enqCnt \in [Values -> Nat]
    /\ deqCnt \in [Values -> Nat]

Init ==
    /\ queue  = << >>
    /\ ret    = [c \in Clients |-> Neutral]
    /\ enqCnt = [v \in Values |-> 0]
    /\ deqCnt = [v \in Values |-> 0]

----------------------------------------------------------------------------------------
(* Enqueue attempts *)

EnqTail(c, v) ==
    /\ ret[c] = Neutral
    /\ Len(queue) < N
    /\ queue'  = Append(queue, v)
    /\ ret'    = [ret EXCEPT ![c] = [op |-> "enq", status |-> "ok", val |-> v]]
    /\ enqCnt' = [enqCnt EXCEPT ![v] = @ + 1]
    /\ UNCHANGED deqCnt

EnqHead(c, v) ==
    /\ ret[c] = Neutral
    /\ Len(queue) < N
    /\ queue'  = <<v>> \o queue
    /\ ret'    = [ret EXCEPT ![c] = [op |-> "enq", status |-> "ok", val |-> v]]
    /\ enqCnt' = [enqCnt EXCEPT ![v] = @ + 1]
    /\ UNCHANGED deqCnt

EnqFull(c, v) ==
    /\ ret[c] = Neutral
    /\ Len(queue) >= N
    /\ ret' = [ret EXCEPT ![c] = [op |-> "enq", status |-> "full", val |-> v]]
    /\ UNCHANGED <<queue, enqCnt, deqCnt>>

EnqSucceed(c) == \E v \in Values : EnqTail(c, v) \/ EnqHead(c, v)

EnqAttempt(c) == \E v \in Values : EnqTail(c, v) \/ EnqHead(c, v) \/ EnqFull(c, v)

----------------------------------------------------------------------------------------
(* Dequeue attempts *)

DeqHead(c) ==
    /\ ret[c] = Neutral
    /\ Len(queue) > 0
    /\ LET v == Head(queue) IN
         /\ queue'  = Tail(queue)
         /\ ret'    = [ret EXCEPT ![c] = [op |-> "deq", status |-> "ok", val |-> v]]
         /\ deqCnt' = [deqCnt EXCEPT ![v] = @ + 1]
    /\ UNCHANGED enqCnt

DeqTail(c) ==
    /\ ret[c] = Neutral
    /\ Len(queue) > 0
    /\ LET v == queue[Len(queue)] IN
         /\ queue'  = SubSeq(queue, 1, Len(queue) - 1)
         /\ ret'    = [ret EXCEPT ![c] = [op |-> "deq", status |-> "ok", val |-> v]]
         /\ deqCnt' = [deqCnt EXCEPT ![v] = @ + 1]
    /\ UNCHANGED enqCnt

DeqEmpty(c) ==
    /\ ret[c] = Neutral
    /\ Len(queue) = 0
    /\ ret' = [ret EXCEPT ![c] = [op |-> "deq", status |-> "empty", val |-> NoVal]]
    /\ UNCHANGED <<queue, enqCnt, deqCnt>>

DeqSucceed(c) == DeqHead(c) \/ DeqTail(c)

DeqAttempt(c) == DeqHead(c) \/ DeqTail(c) \/ DeqEmpty(c)

----------------------------------------------------------------------------------------
(* Reset of local result *)

Reset(c) ==
    /\ ret[c] # Neutral
    /\ ret' = [ret EXCEPT ![c] = Neutral]
    /\ UNCHANGED <<queue, enqCnt, deqCnt>>

ClientNext(c) == EnqAttempt(c) \/ DeqAttempt(c) \/ Reset(c)

Next == \E c \in Clients : ClientNext(c)

Fairness == \A c \in Clients : WF_vars(ClientNext(c))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------------------
(* Safety properties *)

\* The queue length never exceeds N
CapacityBound == Len(queue) <= N

\* Queue contents exactly reflect enqueued-minus-dequeued values:
\* no spurious values and no duplication.
Conservation ==
    \A v \in Values :
        /\ deqCnt[v] <= enqCnt[v]
        /\ Count(queue, v) = enqCnt[v] - deqCnt[v]

\* Every value returned by a dequeue was previously enqueued and not already removed.
DeqReturnsLiveElement ==
    [][\A c \in Clients :
         (ret[c] = Neutral /\ ret'[c].op = "deq" /\ ret'[c].status = "ok")
           => LET v == ret'[c].val IN
                /\ Count(queue, v) >= 1
                /\ deqCnt[v] < enqCnt[v]
                /\ Count(queue', v) = Count(queue, v) - 1
                /\ Len(queue') = Len(queue) - 1
      ]_vars

\* An enqueue reporting success actually places its value into the queue.
EnqSuccessPlacesValue ==
    [][\A c \in Clients :
         (ret[c] = Neutral /\ ret'[c].op = "enq" /\ ret'[c].status = "ok")
           => LET v == ret'[c].val IN
                /\ Len(queue) < N
                /\ Len(queue') = Len(queue) + 1
                /\ Count(queue', v) = Count(queue, v) + 1
                /\ (queue' = Append(queue, v) \/ queue' = <<v>> \o queue)
      ]_vars

\* Failure reports are only given when justified.
FailureJustified ==
    [][\A c \in Clients :
         /\ (ret[c] = Neutral /\ ret'[c].status = "full")  => Len(queue) >= N
         /\ (ret[c] = Neutral /\ ret'[c].status = "empty") => Len(queue) = 0
      ]_vars

----------------------------------------------------------------------------------------
(* Liveness properties *)

\* No client is permanently disabled: every client always eventually acts again.
ClientProgress ==
    \A c \in Clients : []<><<ClientNext(c)>>_vars

\* Every client eventually returns to the neutral state, ready for a new operation.
EventuallyReset ==
    \A c \in Clients : (ret[c] # Neutral) ~> (ret[c] = Neutral)

\* Persistent enqueue attempts while capacity is available eventually succeed.
EnqLiveness ==
    \A c \in Clients :
        ([]<><<EnqAttempt(c) /\ Len(queue) < N>>_vars)
            => []<><<EnqSucceed(c)>>_vars

\* Persistent dequeue attempts while the queue is nonempty eventually succeed.
DeqLiveness ==
    \A c \in Clients :
        ([]<><<DeqAttempt(c) /\ Len(queue) > 0>>_vars)
            => []<><<DeqSucceed(c)>>_vars

----------------------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ CapacityBound /\ Conservation)
THEOREM Spec => DeqReturnsLiveElement /\ EnqSuccessPlacesValue /\ FailureJustified
THEOREM Spec => ClientProgress /\ EventuallyReset /\ EnqLiveness /\ DeqLiveness
========================================================================================