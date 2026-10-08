---------------------------- MODULE ConcurrentQueue ----------------------------

CONSTANTS N \* Maximum capacity of the queue
          Val \* Domain of values that can be enqueued

VARIABLES queue, \* The shared queue
            clientResults \* Local results for each client

\* Initialize the queue to be empty and all client results to a neutral state (e.g., <<>>)
Init == /\ queue = << >>
        /\ clientResults = [c \in ClientSet |-> << >>]

\* Check if the queue is full
QueueFull == Len(queue) >= N

\* Check if the queue is empty
QueueEmpty == Len(queue) = 0

\* Enqueue a value into the queue (either at head or tail)
Enqueue(c, v) ==
    /\ QueueFull -> clientResults' = [clientResults EXCEPT ![c] = "FULL"]
    /\ ~QueueFull ->
        LET newQueueHead == <<v>> \o queue
            newQueueTail == queue \o <<v>>
        IN  \/ /\ queue' = newQueueHead
                /\ clientResults' = [clientResults EXCEPT ![c] = v]
            \/ /\ queue' = newQueueTail
                /\ clientResults' = [clientResults EXCEPT ![c] = v]

\* Dequeue a value from the queue (either from head or tail)
Dequeue(c) ==
    /\ QueueEmpty -> clientResults' = [clientResults EXCEPT ![c] = "EMPTY"]
    /\ ~QueueEmpty ->
        LET dequeuedHead == Head(queue)
            dequeuedTail == Tail(queue)
            newQueueHead == Tail(queue)
            newQueueTail == SubSeq(queue, 1, Len(queue) - 1)
        IN  \/ /\ queue' = newQueueHead
                /\ clientResults' = [clientResults EXCEPT ![c] = dequeuedHead]
            \/ /\ queue' = newQueueTail
                /\ clientResults' = [clientResults EXCEPT ![c] = dequeuedTail]

\* Reset the local result for a client to a neutral state (e.g., <<>>)
Reset(c) ==
    clientResults' = [clientResults EXCEPT ![c] = << >>]

\* Actions that can be performed by each client
ClientActions(c) == \/ \E v \in Val : Enqueue(c, v)
                    \/ Dequeue(c)

\* The next state relation for the system
Next ==
    \E c \in ClientSet :
        /\ ClientActions(c)
        /\ Reset(c)

\* Specification of the system
Spec ==
    Init /\ [][Next]_<<clientResults>>

\* Safety properties
QueueCapacityBound == \A s \in StateSpace : Len(s.queue) <= N

NoSpuriousValues ==
    \A s, s' \in StateSpace, c \in ClientSet :
        /\ Dequeue(c) \land s' = [s EXCEPT queue' = s'.queue]
        -> s'.clientResults[c] \in Val \/ s'.clientResults[c] = "EMPTY"

NoDuplicates ==
    \A s, s', s'' \in StateSpace, c1, c2 \in ClientSet :
        /\ Dequeue(c1) \land s' = [s EXCEPT queue' = s'.queue]
        /\ Dequeue(c2) \land s'' = [s' EXCEPT queue' = s''.queue]
        -> s'.clientResults[c1] # s''.clientResults[c2] \/ s'.clientResults[c1] = "EMPTY" \/ s''.clientResults[c2] = "EMPTY"

EnqueueSuccess ==
    \A s, s', c \in ClientSet, v \in Val :
        /\ Enqueue(c, v) \land s' = [s EXCEPT queue' = s'.queue]
        -> (s'.clientResults[c] = v => v \in s'.queue)

SafetyProperties == QueueCapacityBound /\ NoSpuriousValues /\ NoDuplicates /\ EnqueueSuccess

\* Liveness properties
WF_Queue ==
    \A c \in ClientSet :
        WF_<<c>>_ClientActions(c)

WF_ClientActions(c) ==
    \A s \in StateSpace :
        ~QueueFull -> <>(Enqueue(c, _))_<<clientResults>>
        /\ ~QueueEmpty -> <>(Dequeue(c))_<<clientResults>>

LivenessProperties == WF_Queue

\* Complete specification with safety and liveness properties
Spec ==
    Init /\ [][Next]_<<clientResults>> /\ <>[]SafetyProperties /\ LivenessProperties

=============================================================================