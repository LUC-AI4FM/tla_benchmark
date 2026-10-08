```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs
VARIABLES tickNum, choosing, localexamined, maxseen, pc

Init ==
  /\ tickNum = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ localexamined = [i \in 1..NumProcs |-> {}]
  /\ maxseen = [i \in 1..NumProcs |-> 0]
  /\ pc = [i \in 1..NumProcs |-> "Start"]

Next ==
  (\E i \in 1..NumProcs :
    /\ pc[i] = "Start"
    /\ tickNum' = [tickNum EXCEPT ![i] = tickNum[i] + 1]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ localexamined' = [localexammed EXCEPT ![i] = {}]
    /\ maxseen' = [maxseen EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "TryLock"]
    /\ UNCHANGED <<tickNum, choosing, localexamined, maxseen, pc>>[i \in 1..NumProcs \ {i}]
  )
  \/ (\E i \in 1..NumProcs :
    /\ pc[i] = "TryLock"
    /\ \E j \in 1..NumProcs \ {i} :
      /\ tickNum[j] # 0
      /\ (tickNum[j] < tickNum[i]) \/ (tickNum[j] = tickNum[i] /\ j < i)
      /\ localexamined' = [localexamined EXCEPT ![i] = localexamined[i] \cup {j}]
      /\ maxseen' = [maxseen EXCEPT ![i] = IF maxseen[i] < tickNum[j] THEN tickNum[j] ELSE maxseen[i]]
      /\ pc' = [pc EXCEPT ![i] = "Wait"]
      /\ UNCHANGED <<tickNum, choosing, localexamined, maxseen, pc>>[k \in 1..NumProcs \ {i}]
    )
  \/ (\E i \in 1..NumProcs :
    /\ pc[i] = "Wait"
    /\ \A j \in 1..NumProcs \ {i} : (tickNum[j] = 0) \/ (tickNum[j] > maxseen[i])
    /\ tickNum' = [tickNum EXCEPT ![i] = 0]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ localexamined' = [localexammed EXCEPT ![i] = {}]
    /\ maxseen' = [maxseen EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "Critical"]
    /\ UNCHANGED <<tickNum, choosing, localexamined, maxseen, pc>>[j \in 1..NumProcs \ {i}]
  )
  \/ (\E i \in 1..NumProcs :
    /\ pc[i] = "Critical"
    /\ tickNum' = [tickNum EXCEPT ![i] = 0]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ localexammed' = [localexammed EXCEPT ![i] = {}]
    /\ maxseen' = [maxseen EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<tickNum, choosing, localexamined, maxseen, pc>>[j \in 1..NumProcs \ {i}]
  )

Spec == Init /\ [][Next]_<<tickNum, choosing, localexamined, maxseen, pc>>
WF_Vars == <<pc>>

THEOREM Spec => []<>(\E i \in 1..NumProcs : pc[i] = "Critical")
INVARIANT MutualExclusion == \A i,j \in 1..NumProcs : (pc[i] = "Critical") /\ (pc[j] = "Critical") => i = j

 CONSTRAINT TicketsBound == \A i \in 1..NumProcs : tickNum[i] < NumProcs
```