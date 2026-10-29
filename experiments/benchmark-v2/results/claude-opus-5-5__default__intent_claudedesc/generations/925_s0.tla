------------------------------ MODULE FIFOQueue ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Data,           \* The set of payload values that can be enqueued
    MaxQueueLen     \* Model-checking bound on the queue length (set in the .cfg)

ASSUME /\ Data # {}
       /\ MaxQueueLen \in Nat
       /\ MaxQueueLen >= 1

-----------------------------------------------------------------------------
(***************************************************************************)
(* Each enqueued item is tagged with a sequence id so that ordering, loss  *)
(* and duplication can be checked. Ids are taken modulo N = MaxQueueLen+1. *)
(* This keeps the state space finite. Because the state constraint keeps   *)
(* the queue at or below MaxQueueLen items, the ids in the queue are always *)
(* distinct.                                                               *)
(***************************************************************************)
N   == MaxQueueLen + 1
Ids == 0 .. (N - 1)

Item == [id : Ids, val : Data]

VARIABLES
    queue,      \* The FIFO queue: a sequence of items
    nextIn,     \* Id that will be given to the next enqueued item
    nextOut     \* Id that the next dequeued item is expected to carry

vars == << queue, nextIn, nextOut >>

-----------------------------------------------------------------------------
(*************************** Core queue specification **********************)

TypeOK ==
    /\ queue \in Seq(Item)
    /\ nextIn \in Ids
    /\ nextOut \in Ids

Init ==
    /\ queue = << >>
    /\ nextIn = 0
    /\ nextOut = 0

\* Add an item with payload d to the back of the queue.
Enqueue(d) ==
    /\ queue' = Append(queue, [id |-> nextIn, val |-> d])
    /\ nextIn' = (nextIn + 1) % N
    /\ UNCHANGED nextOut

\* Remove the item at the front of the queue.
Dequeue ==
    /\ queue # << >>
    /\ queue' = Tail(queue)
    /\ nextOut' = (nextOut + 1) % N
    /\ UNCHANGED nextIn

Next ==
    \/ \E d \in Data : Enqueue(d)
    \/ Dequeue

Spec == Init /\ [][Next]_vars

\* Optional fair variant: the consumer cannot stall forever.
FairSpec == Spec /\ WF_vars(Dequeue)

-----------------------------------------------------------------------------
(*************************** Correctness properties ************************)

\* FIFO ordering: the queue holds consecutive ids, starting at the id
\* expected by the next dequeue. So the oldest item is always removed first.
FIFOOrder ==
    \A i \in 1 .. Len(queue) : queue[i].id = (nextOut + i - 1) % N

\* No loss: every item enqueued but not yet dequeued is still in the queue.
NoLoss ==
    Len(queue) = ((nextIn + N) - nextOut) % N

\* No duplication: each enqueued item appears exactly once in the queue.
NoDuplication ==
    \A i, j \in 1 .. Len(queue) : i # j => queue[i].id # queue[j].id

SafetyInvariant ==
    /\ TypeOK
    /\ FIFOOrder
    /\ NoLoss
    /\ NoDuplication

\* Every dequeue removes the item carrying the expected (oldest) id.
DequeueInOrder ==
    [][ (Len(queue') < Len(queue)) => Head(queue).id = nextOut ]_vars

\* No corruption: existing items are never modified. A step either appends
\* to the back while keeping the prefix intact, or removes exactly the head.
NoCorruption ==
    [][ \/ /\ Len(queue') = Len(queue) + 1
           /\ SubSeq(queue', 1, Len(queue)) = queue
        \/ /\ queue # << >>
           /\ queue' = Tail(queue)
      ]_queue

\* Liveness (under FairSpec): the item at the head is eventually dequeued.
HeadEventuallyDequeued ==
    \A k \in Ids :
        (queue # << >> /\ Head(queue).id = k /\ nextOut = k)
            ~> (nextOut # k \/ queue = << >>)

-----------------------------------------------------------------------------
(*************************** Model-checking support ************************)
(* Use as CONSTRAINT in the TLC configuration, e.g.:                       *)
(*   CONSTANTS Data = {d1, d2}  MaxQueueLen = 3                            *)
(*   CONSTRAINT StateConstraint                                            *)
(*   INVARIANT  SafetyInvariant                                            *)
(*   PROPERTIES DequeueInOrder NoCorruption                                *)
StateConstraint == Len(queue) <= MaxQueueLen

THEOREM Spec => []SafetyInvariant
=============================================================================