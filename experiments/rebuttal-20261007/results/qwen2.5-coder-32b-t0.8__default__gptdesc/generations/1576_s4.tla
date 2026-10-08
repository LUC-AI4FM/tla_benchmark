---- MODULE ConcurrentQueue ----

EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N

VARIABLES queue, procState

Init == 
  /\ queue = << >>
  /\ \A p \in Procs: procState[p] = "idle"

P(self) ==
  either
    /\ self \notin {p \in Procs : procState[p] \in {"enq_front", "enq_back"}}
    /\ \/ /\ queue /= << >> 
           /\ (procState[self]' = "deq_head" \/ procState[self]' = "deq_tail")
       \/ /\ queue = << >>
           /\ (procState[self]' = "enq_front" \/ procState[self]' = "enq_back")
  or
    /\ self \notin {p \in Procs : procState[p] \in {"deq_head", "deq_tail"}}
    /\ \/ /\ queue /= << >> 
           /\ (procState[self]' = "enq_front" \/ procState[self]' = "enq_back")
       \/ /\ queue = << >>
           /\ (procState[self]' = "idle")

Next ==
  \E p \in Procs:
    LET action == procState[p] IN
      CASE action = "enq_front" ->
        /\ queue' = << CHOOSE v \in Val: TRUE >> \o queue
        /\ procState'[p] = "idle"
        /\ \A q \in (Procs \ {p}): procState'[q] = procState[q]
      [] action = "enq_back" ->
        /\ queue' = queue \o << CHOOSE v \in Val: TRUE >>
        /\ procState'[p] = "idle"
        /\ \A q \in (Procs \ {p}): procState'[q] = procState[q]
      [] action = "deq_head" ->
        /\ queue /= << >> 
        /\ queue' = Tail(queue)
        /\ procState'[p] = "idle"
        /\ \A q \in (Procs \ {p}): procState'[q] = procState[q]
      [] action = "deq_tail" ->
        /\ queue /= << >>
        /\ queue' = Head(queue)
        /\ procState'[p] = "idle"
        /\ \A q \in (Procs \ {p}): procState'[q] = procState[q]
      [] action = "idle" ->
        /\ queue' = queue
        /\ P(p)
        /\ \A q \in (Procs \ {p}): procState'[q] = procState[q]

Spec ==
  Init /\ [][Next]_<<procState, queue>> /\ WF_<<P>>_(Procs)

QueueBound == Len(queue) <= N

 fairness ==
   \A p \in Procs: WF_<<P(p)>>_

====