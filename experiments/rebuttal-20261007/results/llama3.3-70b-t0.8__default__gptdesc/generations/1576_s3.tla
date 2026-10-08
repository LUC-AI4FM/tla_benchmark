```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init ==
  /\ queue = <<
  /\ rV = [i \in Procs |-> NULL]

Next ==
  \/ \E p \in Procs :
    /\ queue # <<
    /\ \/ (\E v \in Val :
            /\ queue' = <<v>> \o queue
            /\ rV' = [rV EXCEPT ![p] = "okay"])
         \/ (queue' = Tail(queue)
            /\ rV' = [rV EXCEPT ![p] = Head(queue)])
    /\ UNCHANGED rV'[Procs \ {p}]
  \/ \E p \in Procs :
    /\ queue # <<
    /\ \/ (\E v \in Val :
            /\ queue' = Append(queue, v)
            /\ rV' = [rV EXCEPT ![p] = "okay"])
         \/ (queue' = SubSeq(queue, 2, Len(queue))
            /\ rV' = [rV EXCEPT ![p] = queue[Len(queue)]])
    /\ UNCHANGED rV'[Procs \ {p}]

Spec ==
  /\ Init
  /\ [][Next]_<<queue, rV>>
  /\ WF_(self \in Procs, P(self))_
      <<queue, rV>>

P(self) ==
  /\ queue # <<
  /\ \/ (\E v \in Val :
          /\ queue = <<v>> \o queue
          /\ rV = [rV EXCEPT ![self] = "okay"])
     \/ (queue = Tail(queue)
        /\ rV = [rV EXCEPT ![self] = Head(queue)])
  /\ UNCHANGED rV[Procs \ {self}]

QueueLenInv ==
  Len(queue) <= N

THEOREM Spec => []QueueLenInv
```