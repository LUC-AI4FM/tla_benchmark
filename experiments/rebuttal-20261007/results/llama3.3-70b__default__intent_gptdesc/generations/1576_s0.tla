```
MODULE QueueService
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
  N,  \* maximum capacity of the queue
  Clients,  \* set of client identifiers
  Values    \* value domain

VARIABLES
  queue,  \* the shared queue
  results,  \* per-client return values
  attempts  \* per-client operation attempts (enqueue or dequeue)

Init ==
  /\ queue = <<>>
  /\ results = [c \in Clients |-> "neutral"]
  /\ attempts = [c \in Clients |-> "none"]

Next ==
  \E c \in Clients :
    \/ Enqueue(c)
    \/ Dequeue(c)
    \/ Reset(c)

Enqueue(c) ==
  /\ attempts[c] = "enqueue"
  /\ \E v \in Values, pos \in {1, Length(queue) + 1} :
      /\ queue' = Insert(queue, pos, v)
      /\ results' = [results EXCEPT ![c] = IF Length(queue') > N THEN "full" ELSE "success"]
      /\ attempts' = [attempts EXCEPT ![c] = "none"]
      /\ UNCHANGED << >>

Dequeue(c) ==
  /\ attempts[c] = "dequeue"
  /\ \E pos \in {1, Length(queue)} :
      /\ queue' = Remove(queue, pos)
      /\ results' = [results EXCEPT ![c] = IF queue = <<>> THEN "empty" ELSE Head(Tail(queue, pos - 1))]
      /\ attempts' = [attempts EXCEPT ![c] = "none"]
      /\ UNCHANGED << >>

Reset(c) ==
  /\ attempts[c] = "none"
  /\ results' = [results EXCEPT ![c] = "neutral"]
  /\ queue' = queue
  /\ attempts' = attempts

Spec ==
  Init /\ [][Next]_queue /\ [][Next]_results /\ [][Next]_attempts

QueueLenInv == Length(queue) <= N
NoSpuriousValues == \A c \in Clients : results[c] \in {"neutral", "full", "empty", "success"} \/ results[c] \in Values
NoDuplication == \A c1, c2 \in Clients : results[c1] = results[c2] => c1 = c2
SuccessImpliesEnqueue == \A c \in Clients : results[c] = "success" => \E pos \in {1, Length(queue) + 1} : queue[pos] = results[c]

THEOREM Spec => []QueueLenInv
THEOREM Spec => []NoSpuriousValues
THEOREM Spec => []NoDuplication
THEOREM Spec => []SuccessImpliesEnqueue

Fairness ==
  \A c \in Clients :
    WF_Attempts(c) /\ SF_Attempts(c)

WF_Attempts(c) == <>[]attempts[c] = "none"
SF_Attempts(c) == []<>attempts[c] = "enqueue" \/ attempts[c] = "dequeue"

THEOREM Spec => Fairness
```