```
MODULE ConcurrentQueue
EXTENDS Integers, Sequences, TLC

CONSTANTS Values, Processes, N
VARIABLES queue, results, processStates

Init ==
  /\ queue = <<>>
  /\ results = [p \in Processes |-> NULL]
  /\ processStates = [p \in Processes |-> "idle"]

Next ==
  (\E p \in Processes :
    /\ processStates[p] = "idle"
    /\ results[p] = NULL
    /\ ( 
        /\ queue # <<>> 
        /\ results' = [results EXCEPT ![p] = "empty"]
        /\ queue' = queue
        /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
      \/
      ( 
        /\ Len(queue) < N 
        /\ \E v \in Values :
          /\ results' = [results EXCEPT ![p] = "success"]
          /\ queue' = Append(<<v>>, queue)
          /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
      \/
      ( 
        /\ Len(queue) < N 
        /\ \E v \in Values :
          /\ results' = [results EXCEPT ![p] = "success"]
          /\ queue' = <<v>> \o queue
          /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
      \/
      ( 
        /\ Len(queue) = N 
        /\ results' = [results EXCEPT ![p] = "full"]
        /\ queue' = queue
        /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
      \/
      ( 
        /\ queue # <<>> 
        /\ \E v \in Values :
          /\ results' = [results EXCEPT ![p] = v]
          /\ queue' = Tail(queue)
          /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
      \/
      ( 
        /\ queue # <<>> 
        /\ \E v \in Values :
          /\ results' = [results EXCEPT ![p] = v]
          /\ queue' = SubSeq(queue, 2, Len(queue))
          /\ processStates' = [processStates EXCEPT ![p] = "done"]
      )
    )
  )

Spec ==
  /\ Init
  /\ [][Next]_queue
  /\ WF_vars(Next, processStates)

THEOREM Spec => []Len(queue) <= N

THEOREM Spec => WF_vars(Next, processStates)
```