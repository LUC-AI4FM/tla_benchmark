```tla
MODULE ConcurrentQueue

EXTENDS Naturals, Sequences, TLC

CONSTANTS Procs, Val, N

VARIABLES queue, procsState

procsState == [p \in Procs |> [action: {"enqueueFront", "enqueueBack", "dequeueFront", "dequeueBack"}, rV: {"okay", "full", "empty"} \cup Val]]

Init ==
    /\ queue = << >>
    /\ (\A p \in Procs: procsState[p] = [action |-> "enqueueFront", rV |-> "null"])

Next ==
    \/ /\ E\<exists> p \in Procs :
          LET s == procsState[p]
              q' == CASE s.action = "enqueueFront" -> <<s.rV>> \o queue
                      [] s.action = "enqueueBack"  -> queue \o <<s.rV>>
                      [] s.action = "dequeueFront" -> IF queue /= << >> THEN Tail(queue) ELSE queue
                      [] s.action = "dequeueBack"  -> IF queue /= << >> THEN SubSeq(queue, 1, Len(queue)-1) ELSE queue
              r' == CASE s.action = "enqueueFront" /\ Len(queue) >= N -> "full"
                      [] s.action = "enqueueBack"  /\ Len(queue) >= N -> "full"
                      [] s.action = "dequeueFront" /\ queue /= << >> -> Head(queue)
                      [] s.action = "dequeueBack"  /\ queue /= << >> -> Last(queue)
                      [] s.action \in {"dequeueFront", "dequeueBack"} /\ queue = << >> -> "empty"
                      [] ELSE "okay"
          IN
              \/ /\ s.rV \notin Val
                 /\ q' = queue
                 /\ r' = "okay"
                 /\ procsState' = [procsState EXCEPT ![p].rV = r']
              \/ /\ s.rV \in Val \/ s.action \in {"dequeueFront", "dequeueBack"}
                 /\ queue' = q'
                 /\ procsState' = [procsState EXCEPT ![p].rV = r']

Spec ==
    /\ Init
    /\ [][Next]_<<queue, procsState>>
    /\ WF_<<procsState>>_(\E p \in Procs: {p})
    /\ /\A queue : Len(queue) <= N

```