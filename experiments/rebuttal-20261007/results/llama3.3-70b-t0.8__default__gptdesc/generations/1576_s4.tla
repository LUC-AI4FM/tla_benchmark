```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init == 
  (queue = <<>>) /\ (rV = [i \in Procs |-> NULL])

Next == 
  (\E p \in Procs : 
    (/\ rV[p] = NULL
     /\ (\/ EnqueueFront(p)
          \/ EnqueueBack(p)
          \/ DequeueHead(p)
          \/ DequeueTail(p))))

EnqueueFront(p) == 
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = "full"]
   /\ queue' = <<>>)
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "full"]
   /\ queue' = <<>>)
  \/
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = "okay"]
   /\ queue' = Append(Prepend(queue, ChooseVal(p)), SubSeq(queue, 2, Len(queue))))
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "okay"]
   /\ queue' = Prepend(queue, ChooseVal(p)))

EnqueueBack(p) == 
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = "full"]
   /\ queue' = <<>>)
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "full"]
   /\ queue' = <<>>)
  \/
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = "okay"]
   /\ queue' = Append(queue, ChooseVal(p)))
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "okay"]
   /\ queue' = <<ChooseVal(p)>>)

DequeueHead(p) == 
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = Head(queue)]
   /\ queue' = SubSeq(queue, 2, Len(queue)))
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "empty"]
   /\ queue' = <<>>)

DequeueTail(p) == 
  (/\ queue /= <<>>
   /\ rV' = [rV EXCEPT ![p] = Last(queue)]
   /\ queue' = SubSeq(queue, 1, Len(queue) - 1))
  \/
  (/\ queue = <<>>
   /\ rV' = [rV EXCEPT ![p] = "empty"]
   /\ queue' = <<>>)

ChooseVal(p) == 
  CHOOSE v \in Val : TRUE

Spec == Init /\ [][Next]_queue /\ [][Next]_rV
        /\ WF_vars(EnqueueFront(self)) /\ WF_vars(EnqueueBack(self))
        /\ WF_vars(DequeueHead(self)) /\ WF_vars(DequeueTail(self))

THEOREM Spec => []Len(queue) <= N

END QueueSystem
```