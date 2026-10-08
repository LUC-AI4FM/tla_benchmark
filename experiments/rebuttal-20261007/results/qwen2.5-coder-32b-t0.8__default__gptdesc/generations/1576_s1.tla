```tla
MODULE ConcurrentQueue

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Procs, Val, N

VARIABLES queue, rV \* rV is a function from Procs to { "okay", "full", "empty" } \/ Val

Init == /\ queue = << >>
        /\ rV \in [Procs -> {"okay", "full", "empty"}]

EnqueueAtFront(self, val) ==
    /\ val \in Val
    /\ Len(queue) < N
    /\ queue' = <<val>> \o queue
    /\ rV' = [rV EXCEPT ![self] = "okay"]

EnqueueAtBack(self, val) ==
    /\ val \in Val
    /\ Len(queue) < N
    /\ queue' = queue \o <<val>>
    /\ rV' = [rV EXCEPT ![self] = "okay"]

DequeueFromHead(self) ==
    /\ Len(queue) > 0
    /\ queue' = Tail(queue)
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]

DequeueFromTail(self) ==
    /\ Len(queue) > 0
    /\ queue' = SubSeq(queue, 1, Len(queue)-1)
    /\ rV' = [rV EXCEPT ![self] = Last(queue)]

DequeueAction(self) ==
    \/ DequeueFromHead(self)
    \/ DequeueFromTail(self)

EnqueueAction(self) ==
    \/ EnqueueAtFront(self, CHOOSE val \in Val : TRUE)
    \/ EnqueueAtBack(self, CHOOSE val \in Val : TRUE)

ProcAction(self) ==
    \/ DequeueAction(self)
    \/ EnqueueAction(self)

Next == \E self \in Procs: ProcAction(self)

Spec ==
    /\ Init
    /\ [][Next]_<<queue, rV>>
    /\ WF_[Procs -> {DequeueFromHead, DequeueFromTail}]_(ProcAction)
    /\ WF_[Procs -> {EnqueueAtFront, EnqueueAtBack}]_(ProcAction)

QueueLengthBound == Len(queue) \leq N
```