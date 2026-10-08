```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init == 
  (queue = <<>>) /\ 
  (rV = [i \in Procs |-> NULL])

Next == 
  (\E i \in Procs : 
    (\/ EnqueueFront(i) 
     \/ EnqueueBack(i) 
     \/ DequeueHead(i) 
     \/ DequeueTail(i)))

EnqueueFront(p) == 
  (rV' = [rV EXCEPT ![p] = "okay"]) /\ 
  (queue' = Prepend(queue, ChooseVal(p))) /\ 
  UNCHANGED << >>

EnqueueBack(p) == 
  (rV' = [rV EXCEPT ![p] = "okay"]) /\ 
  (queue' = Append(queue, ChooseVal(p))) /\ 
  UNCHANGED << >>

DequeueHead(p) == 
  (queue # <<>>) /\ 
  (rV' = [rV EXCEPT ![p] = Head(queue)]) /\ 
  (queue' = Tail(queue)) /\ 
  UNCHANGED << >>

DequeueTail(p) == 
  (queue # <<>>) /\ 
  (rV' = [rV EXCEPT ![p] = Last(queue)]) /\ 
  (queue' = SubSeq(queue, 1, Len(queue) - 1)) /\ 
  UNCHANGED << >>

ChooseVal(p) == 
  CHOOSE v \in Val : TRUE

Spec == 
  Init /\ [][Next]_<<queue, rV>> 

QueueLenInv == 
  Len(queue) <= N

THEOREM Spec => []QueueLenInv
THEOREM Spec => WF_(EnqueueFront(p), <<queue, rV>>) \* [i \in Procs]
THEOREM Spec => WF_(EnqueueBack(p), <<queue, rV>>) \* [i \in Procs]
THEOREM Spec => WF_(DequeueHead(p), <<queue, rV>>) \* [i \in Procs]
THEOREM Spec => WF_(DequeueTail(p), <<queue, rV>>) \* [i \in Procs]

```
Note: This TLA+ module uses the `TLC` (Temporal Logic of Actions) extension for expressing temporal properties and fairness conditions. The `ChooseVal(p)` action is modeled using a non-deterministic choice (`CHOOSE`) from the set of values `Val`. The queue length invariant `QueueLenInv` ensures that the queue does not grow beyond the specified bound `N`.