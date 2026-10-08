```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init ==
  /\ queue = <<>>
  /\ rV = [i \in Procs |-> NULL]

Next ==
  (\E i \in Procs :
    \/ (queue # <<>> /\ rV[i] = "empty")
      /\ queue' = queue
      /\ rV' = [rV EXCEPT ![i] = "empty"]
    \/ (Len(queue) < N)
      /\ \E v \in Val :
        \/ queue' = Append(<<v>>, queue)
          /\ rV' = [rV EXCEPT ![i] = "okay"]
        \/ queue' = Append(queue, <<v>>)
          /\ rV' = [rV EXCEPT ![i] = "okay"]
    \/ (queue # <<>>) 
      /\ \E v \in Val :
        \/ (Head(queue) = v)
          /\ queue' = Tail(queue)
          /\ rV' = [rV EXCEPT ![i] = v]
        \/ (Last(queue) = v)
          /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
          /\ rV' = [rV EXCEPT ![i] = v]
    \/ (Len(queue) = N)
      /\ rV' = [rV EXCEPT ![i] = "full"]
      /\ queue' = queue
  )
  /\ \A j \in Procs \ {i} :
    queue' = queue
    /\ rV' = [rV EXCEPT ![j] = rV[j]]

Spec ==
  Init /\ [][Next]_queue /\ [][Next]_rV

THEOREM Spec => []Len(queue) <= N

Fairness == 
  \A i \in Procs : WF_vars(Next, queue, rV)
```
Note: The `TLC` module is extended to allow the use of the `Len`, `Append`, `Head`, `Tail`, `Last`, and `SubSeq` operators.