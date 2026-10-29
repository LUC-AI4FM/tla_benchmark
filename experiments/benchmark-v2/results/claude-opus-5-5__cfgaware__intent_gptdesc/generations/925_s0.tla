------------------------------ MODULE InnerFIFO ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Message,   \* finite domain of messages
          qLen       \* fixed maximum capacity, chosen at instantiation time

ASSUME qLen \in Nat /\ qLen > 0

VARIABLES q,          \* contents of the FIFO buffer (head = q[1])
          enqueued,   \* history of all successfully enqueued messages
          delivered,  \* history of all successfully dequeued messages
          result      \* outcome of the most recent client request

vars == <<q, enqueued, delivered, result>>

Clients == {"c1", "c2"}

Ops      == {"none", "enq", "deq"}
Statuses == {"none", "ok", "full", "empty"}

Results == [client : Clients \cup {"none"},
            op     : Ops,
            status : Statuses,
            msg    : SUBSET Message]

NoResult == [client |-> "none", op |-> "none", status |-> "none", msg |-> {}]

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ q \in Seq(Message)
    /\ enqueued \in Seq(Message)
    /\ delivered \in Seq(Message)
    /\ result \in Results

Init ==
    /\ q = << >>
    /\ enqueued = << >>
    /\ delivered = << >>
    /\ result = NoResult

-----------------------------------------------------------------------------
\* Enqueue succeeds only when capacity permits.
Enqueue(c, m) ==
    /\ Len(q) < qLen
    /\ q' = Append(q, m)
    /\ enqueued' = Append(enqueued, m)
    /\ result' = [client |-> c, op |-> "enq", status |-> "ok", msg |-> {m}]
    /\ UNCHANGED delivered

\* Enqueue is rejected when the queue is full.
EnqueueRejected(c, m) ==
    /\ Len(q) = qLen
    /\ result' = [client |-> c, op |-> "enq", status |-> "full", msg |-> {m}]
    /\ UNCHANGED <<q, enqueued, delivered>>

\* Dequeue succeeds only when the queue is nonempty, returning the head.
Dequeue(c) ==
    /\ q # << >>
    /\ q' = Tail(q)
    /\ delivered' = Append(delivered, Head(q))
    /\ result' = [client |-> c, op |-> "deq", status |-> "ok", msg |-> {Head(q)}]
    /\ UNCHANGED enqueued

\* Dequeue on an empty queue returns an "empty" indication.
DequeueEmpty(c) ==
    /\ q = << >>
    /\ result' = [client |-> c, op |-> "deq", status |-> "empty", msg |-> {}]
    /\ UNCHANGED <<q, enqueued, delivered>>

EnqueueOK  == \E c \in Clients, m \in Message : Enqueue(c, m)
DequeueOK  == \E c \in Clients : Dequeue(c)

Next ==
    \/ \E c \in Clients, m \in Message : Enqueue(c, m) \/ EnqueueRejected(c, m)
    \/ \E c \in Clients : Dequeue(c) \/ DequeueEmpty(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(DequeueOK) /\ WF_vars(EnqueueOK)

-----------------------------------------------------------------------------
\* State constraint for bounding model checking.
qConstraint == Len(enqueued) <= 2 * qLen

-----------------------------------------------------------------------------
\* Safety properties

IsPrefix(s, t) == Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))

\* Delivered messages form a prefix of the enqueued messages.
DeliveredPrefix == IsPrefix(delivered, enqueued)

\* No silent loss: every enqueued message is either delivered or retained.
NoLoss == enqueued = delivered \o q

\* FIFO ordering: the queue holds exactly the not-yet-delivered suffix, in order.
FIFOOrder == q = SubSeq(enqueued, Len(delivered) + 1, Len(enqueued))

\* Capacity bound.
CapacityBound == Len(q) <= qLen

\* No duplicates: message count is conserved (nothing delivered twice or created).
NoDuplicates == Len(enqueued) = Len(delivered) + Len(q)

\* Explicit enabledness conditions for full / empty queue.
EnabledWhenFull  == Len(q) = qLen =>
                      /\ ~ENABLED EnqueueOK
                      /\ ENABLED DequeueOK
EnabledWhenEmpty == q = << >> =>
                      /\ ~ENABLED DequeueOK
                      /\ ENABLED EnqueueOK

Safety ==
    /\ TypeInvariant
    /\ DeliveredPrefix
    /\ NoLoss
    /\ FIFOOrder
    /\ CapacityBound
    /\ NoDuplicates

-----------------------------------------------------------------------------
\* Liveness properties (under weak fairness)

\* A nonempty queue is eventually drained by at least one dequeue.
DequeueProgress ==
    \A n \in 1..(2 * qLen) :
        (Len(delivered) < n /\ n <= Len(enqueued)) ~> (Len(delivered) >= n)

\* A nonempty queue eventually delivers something.
EventuallyDelivers == (q # << >>) ~> (result.op = "deq" /\ result.status = "ok")

=============================================================================