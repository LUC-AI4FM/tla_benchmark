-------------------------------- MODULE BoundedQueueService --------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Clients,      \* The fixed set of clients
    Values,       \* The value domain for queue elements
    N             \* Maximum capacity of the queue

ASSUME N \in Nat /\ N > 0
ASSUME Clients # {}
ASSUME Values # {}

\* Return values for client operations
CONSTANTS 
    Neutral,      \* No pending result
    Success,      \* Operation succeeded
    QueueFull,    \* Enqueue failed - queue at capacity
    QueueEmpty    \* Dequeue failed - queue was empty

ASSUME Neutral \notin Values
ASSUME Success \notin Values
ASSUME QueueFull \notin Values
ASSUME QueueEmpty \notin Values

VARIABLES
    queue,        \* The shared queue (as a sequence)
    result,       \* Per-client return value: Neutral, Success, QueueFull, QueueEmpty, or a dequeued value
    history       \* Ghost variable: multiset tracking net enqueued values (for specification purposes)

vars == <<queue, result, history>>

\* Type invariant
TypeOK ==
    /\ queue \in Seq(Values)
    /\ Len(queue) <= N
    /\ result \in [Clients -> Values \cup {Neutral, Success, QueueFull, QueueEmpty}]
    /\ history \in [Values -> Nat]

\* Helper: Add element to multiset
AddToHistory(h, v) == [h EXCEPT ![v] = @ + 1]

\* Helper: Remove element from multiset (with floor at 0)
RemoveFromHistory(h, v) == [h EXCEPT ![v] = IF @ > 0 THEN @ - 1 ELSE 0]

\* Initial state
Init ==
    /\ queue = <<>>
    /\ result = [c \in Clients |-> Neutral]
    /\ history = [v \in Values |-> 0]

\* Client c attempts to enqueue value v
\* Nondeterministically chooses to add at head or tail
EnqueueAttempt(c, v) ==
    /\ result[c] = Neutral
    /\ v \in Values
    /\ IF Len(queue) < N
       THEN \/ \* Append at tail
             /\ queue' = Append(queue, v)
             /\ result' = [result EXCEPT ![c] = Success]
             /\ history' = AddToHistory(history, v)
            \/ \* Insert at head
             /\ queue' = <<v>> \o queue
             /\ result' = [result EXCEPT ![c] = Success]
             /\ history' = AddToHistory(history, v)
       ELSE \* Queue is full
             /\ result' = [result EXCEPT ![c] = QueueFull]
             /\ UNCHANGED <<queue, history>>

\* Client c attempts to dequeue
\* Nondeterministically chooses to remove from head or tail
DequeueAttempt(c) ==
    /\ result[c] = Neutral
    /\ IF queue # <<>>
       THEN \/ \* Remove from head
             /\ result' = [result EXCEPT ![c] = Head(queue)]
             /\ history' = RemoveFromHistory(history, Head(queue))
             /\ queue' = Tail(queue)
            \/ \* Remove from tail
             /\ result' = [result EXCEPT ![c] = queue[Len(queue)]]
             /\ history' = RemoveFromHistory(history, queue[Len(queue)])
             /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       ELSE \* Queue is empty
             /\ result' = [result EXCEPT ![c] = QueueEmpty]
             /\ UNCHANGED <<queue, history>>

\* Client c resets its result to neutral
Reset(c) ==
    /\ result[c] # Neutral
    /\ result' = [result EXCEPT ![c] = Neutral]
    /\ UNCHANGED <<queue, history>>

\* Client action: enqueue attempt with some value, or dequeue attempt, or reset
ClientAction(c) ==
    \/ \E v \in Values : EnqueueAttempt(c, v)
    \/ DequeueAttempt(c)
    \/ Reset(c)

\* Next state relation
Next == \E c \in Clients : ClientAction(c)

\* Fairness: weak fairness for each client's actions
Fairness == \A c \in Clients : WF_vars(ClientAction(c))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* S1: Queue length never exceeds N
CapacityBound == Len(queue) <= N

\* S2: Elements returned by dequeues were previously enqueued and not already removed
\* This is ensured by the history ghost variable - we never return a value unless
\* it has positive count in history, and we decrement on dequeue
\* Invariant: history counts are always non-negative and match queue contents
HistoryConsistent ==
    \A v \in Values : 
        history[v] = Len(SelectSeq(queue, LAMBDA x : x = v))

\* S3: Dequeued values are from Values (not spurious)
\* Any non-control result must be a value that was in the queue
ValidResults ==
    \A c \in Clients :
        result[c] \in {Neutral, Success, QueueFull, QueueEmpty} \cup Values

\* Combined safety invariant
SafetyInvariant == 
    /\ TypeOK
    /\ CapacityBound
    /\ HistoryConsistent
    /\ ValidResults

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* L1: If a client persistently attempts enqueue while queue has capacity, 
\*     eventually some enqueue succeeds
\* Expressed as: if queue is not full infinitely often and client is trying,
\* then eventually an enqueue succeeds

\* Helper: Client c is ready to perform an operation (result is neutral)
ClientReady(c) == result[c] = Neutral

\* Helper: An enqueue by client c succeeds (result becomes Success after enqueue)
EnqueueSucceeds(c) == 
    /\ result[c] = Neutral
    /\ result'[c] = Success
    /\ Len(queue') > Len(queue)

\* Helper: A dequeue by client c succeeds (result becomes a value)
DequeueSucceeds(c) ==
    /\ result[c] = Neutral
    /\ result'[c] \in Values
    /\ Len(queue') < Len(queue)

\* L1: If queue has capacity and some client is ready, eventually something happens
EnqueueLiveness ==
    \A c \in Clients :
        []<>(ClientReady(c) /\ Len(queue) < N) => []<>(\E d \in Clients : EnqueueSucceeds(d))

\* L2: If queue is nonempty and some client is ready, eventually a dequeue succeeds
DequeueLiveness ==
    \A c \in Clients :
        []<>(ClientReady(c) /\ queue # <<>>) => []<>(\E d \in Clients : DequeueSucceeds(d))

\* L3: No client is permanently stuck - if enabled, eventually makes progress
\* This follows from weak fairness of ClientAction
ClientProgress ==
    \A c \in Clients :
        [](result[c] # Neutral => <>( result[c] = Neutral))

================================================================================