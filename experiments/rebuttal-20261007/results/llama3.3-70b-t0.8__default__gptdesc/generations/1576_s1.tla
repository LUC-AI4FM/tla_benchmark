```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init ==
  /\ queue = <<>>
  /\ rV = [i \in Procs |-> NULL]

Next ==
  (\E p \in Procs :
    /\ (rV[p] = "okay") 
    /\ (Len(queue) < N)
    /\ (queue' = Append(queue, ChooseVal(Val)))
    /\ (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (UNCHANGED << >>)
  )
  \/
  (\E p \in Procs :
    /\ (rV[p] = "okay")
    /\ (Len(queue) < N)
    /\ (queue' = Prepend(ChooseVal(Val), queue))
    /\ (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (UNCHANGED << >>)
  )
  \/
  (\E p \in Procs :
    /\ (rV[p] = "okay")
    /\ (queue # <<>>)
    /\ (queue' = Tail(queue))
    /\ (rV' = [rV EXCEPT ![p] = Head(queue)])
    /\ (UNCHANGED << >>)
  )
  \/
  (\E p \in Procs :
    /\ (rV[p] = "okay")
    /\ (queue # <<>>)
    /\ (queue' = SubSeq(queue, 2, Len(queue)))
    /\ (rV' = [rV EXCEPT ![p] = queue[1]])
    /\ (UNCHANGED << >>)
  )
  \/
  (\E p \in Procs :
    /\ (rV[p] = "okay")
    /\ (Len(queue) = N)
    /\ (queue' = queue)
    /\ (rV' = [rV EXCEPT ![p] = "full"])
    /\ (UNCHANGED << >>)
  )
  \/
  (\E p \in Procs :
    /\ (rV[p] = "okay")
    /\ (queue = <<>>)
    /\ (queue' = queue)
    /\ (rV' = [rV EXCEPT ![p] = "empty"])
    /\ (UNCHANGED << >>)
  )

Spec ==
  /\ Init
  /\ [][Next]_<<queue, rV>>
  /\ WF_(\E p \in Procs : TRUE, Next)

THEOREM Spec => []Len(queue) <= N

ChooseVal(s) == CHOOSE v \in s : TRUE
```