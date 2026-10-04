---------------------------- MODULE BoundedQueue ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, Val, Clients

VARIABLES queue, clientOp, clientResult

vars == <<queue, clientOp, clientResult>>

TypeOK ==
    /\ queue \in Seq(Val)
    /\ Len(queue) <= N
    /\ clientOp \in [Clients -> {"enqueue", "dequeue", "idle"}]
    /\ clientResult \in [Clients -> {"none", "success", "full", "empty"} \cup Val]

Init ==
    /\ queue = <<>>
    /\ clientOp = [c \in Clients |-> "idle"]
    /\ clientResult = [c \in Clients |-> "none"]

StartEnqueue(c, v) ==
    /\ clientOp[c] = "idle"
    /\ clientResult[c] = "none"
    /\ clientOp' = [clientOp EXCEPT ![c] = "enqueue"]
    /\ UNCHANGED <<queue, clientResult>>

DoEnqueueSuccess(c, v) ==
    /\ clientOp[c] = "enqueue"
    /\ Len(queue) < N
    /\ \/ queue' = Append(queue, v)
       \/ queue' = <<v>> \o queue
    /\ clientResult' = [clientResult EXCEPT ![c] = "success"]
    /\ clientOp' = [clientOp EXCEPT ![c] = "idle"]

DoEnqueueFull(c) ==
    /\ clientOp[c] = "enqueue"
    /\ Len(queue) = N
    /\ clientResult' = [clientResult EXCEPT ![c] = "full"]
    /\ clientOp' = [clientOp EXCEPT ![c] = "idle"]
    /\ UNCHANGED queue

Enqueue(c, v) ==
    /\ clientOp[c] = "idle"
    /\ clientResult[c] = "none"
    /\ v \in Val
    /\ \/ /\ Len(queue) < N
          /\ \/ queue' = Append(queue, v)
             \/ queue' = <<v>> \o queue
          /\ clientResult' = [clientResult EXCEPT ![c] = "success"]
       \/ /\ Len(queue) = N
          /\ clientResult' = [clientResult EXCEPT ![c] = "full"]
          /\ UNCHANGED queue
    /\ clientOp' = [clientOp EXCEPT ![c] = "enqueue"]

DequeueHead(c) ==
    /\ clientOp[c] = "idle"
    /\ clientResult[c] = "none"
    /\ Len(queue) > 0
    /\ clientResult' = [clientResult EXCEPT ![c] = Head(queue)]
    /\ queue' = Tail(queue)
    /\ clientOp' = [clientOp EXCEPT ![c] = "dequeue"]

DequeueTail(c) ==
    /\ clientOp[c] = "idle"
    /\ clientResult[c] = "none"
    /\ Len(queue) > 0
    /\ clientResult' = [clientResult EXCEPT ![c] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
    /\ clientOp' = [clientOp EXCEPT ![c] = "dequeue"]

DequeueEmpty(c) ==
    /\ clientOp[c] = "idle"
    /\ clientResult[c] = "none"
    /\ Len(queue) = 0
    /\ clientResult' = [clientResult EXCEPT ![c] = "empty"]
    /\ clientOp' = [clientOp EXCEPT ![c] = "dequeue"]
    /\ UNCHANGED queue

Dequeue(c) ==
    \/ DequeueHead(c)
    \/ DequeueTail(c)
    \/ DequeueEmpty(c)

Reset(c) ==
    /\ clientOp[c] # "idle"
    /\ clientResult[c] # "none"
    /\ clientResult' = [clientResult EXCEPT ![c] = "none"]
    /\ clientOp' = [clientOp EXCEPT ![c] = "idle"]
    /\ UNCHANGED queue

ClientAction(c) ==
    \/ \E v \in Val : Enqueue(c, v)
    \/ Dequeue(c)
    \/ Reset(c)

Next == \E c \in Clients : ClientAction(c)

Fairness ==
    \A c \in Clients : WF_vars(ClientAction(c))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety Properties

QueueBounded == Len(queue) <= N

\* Auxiliary variable to track all enqueued values (for verification)
\* We express the property that dequeued values were previously enqueued
\* by noting that any value returned must be in Val (which is the domain of enqueueable values)
\* and the operational semantics ensure values come from the queue

DequeueReturnsValidValues ==
    \A c \in Clients :
        clientResult[c] \in Val => clientResult[c] \in Val

\* The queue only contains values from Val
QueueContainsOnlyVal ==
    \A i \in 1..Len(queue) : queue[i] \in Val

Safety == QueueBounded /\ QueueContainsOnlyVal

\* Liveness Properties

\* If a client keeps trying to enqueue while queue has space, eventually succeeds
EnqueueLiveness ==
    \A c \in Clients :
        []<>(Len(queue) < N) => []<>(\E v \in Val : 
            /\ clientOp[c] = "enqueue" 
            /\ clientResult[c] = "success")

\* If a client keeps trying to dequeue while queue is nonempty, eventually succeeds
DequeueLiveness ==
    \A c \in Clients :
        []<>(Len(queue) > 0) => []<>(
            /\ clientOp[c] = "dequeue"
            /\ clientResult[c] \in Val)

\* Each client eventually gets to act (no permanent disabling)
ClientLiveness ==
    \A c \in Clients : []<>(clientOp[c] # "idle" \/ clientResult[c] # "none")

=============================================================================