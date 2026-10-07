```
MODULE Deque
EXTENDS Integers, Sequences

CONSTANTS Val, Procs, null, N
VARIABLES queue, rV

Init == 
  (queue = <<>>) /\ (rV = [p \in Procs |-> null])

L1Enqueue(p) == 
  (\E v \in Val : 
    ((queue' = Append(queue, v)) \/ (queue' = Prepend(v, queue))) /\ 
    (rV' = [rV EXCEPT ![p] = "full"]) \/ 
    (queue' = queue) /\ (rV' = [rV EXCEPT ![p] = "full"]))

L1Dequeue(p) == 
  ((queue # <<>>) /\ 
   (((queue' = Tail(queue)) /\ (rV' = [rV EXCEPT ![p] = Head(queue)])) \/
    ((queue' = SubSeq(queue, 2, Len(queue))) /\ (rV' = [rV EXCEPT ![p] = Last(queue)])))) \/
  ((queue = <<>>) /\ (queue' = queue) /\ (rV' = [rV EXCEPT ![p] = "empty"]))

L1(p) == L1Enqueue(p) \/ L1Dequeue(p)

L2(p) == 
  (queue' = queue) /\ (rV' = [rV EXCEPT ![p] = null])

Next(p) == L1(p) \/ L2(p)

Spec == Init /\ [][Next(p1)]

WF_L1(p) == []<><L1(p)>_queue
WF_L2(p) == []<><L2(p)>_queue

THEOREM Spec => []WF_L1(p1)
THEOREM Spec => []WF_L2(p1)

Inv == Len(queue) <= N

THEOREM Spec => []Inv
```