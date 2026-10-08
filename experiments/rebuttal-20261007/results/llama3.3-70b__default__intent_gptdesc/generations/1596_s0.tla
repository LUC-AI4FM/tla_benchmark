```tla
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, flag, announced, inCS

Init ==
  /\ pc = [i \in 1..N |-> "Start"]
  /\ flag = [i \in 1..N |-> FALSE]
  /\ announced = {}
  /\ inCS = {}

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "Start"
      /\ pc' = [pc EXCEPT ![i] = "Announce"]
      /\ flag' = [flag EXCEPT ![i] = TRUE]
      /\ announced' = announced \cup {i}
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ pc[i] = "Announce"
      /\ \E j \in announced \ {i} : flag[j]
      /\ pc' = [pc EXCEPT ![i] = "Backoff"]
      /\ flag' = [flag EXCEPT ![i] = FALSE]
      /\ announced' = announced \ {i}
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ pc[i] = "Announce"
      /\ ~\E j \in announced \ {i} : flag[j]
      /\ pc' = [pc EXCEPT ![i] = "EnterCS"]
      /\ flag' = flag
      /\ announced' = announced
      /\ inCS' = inCS \cup {i}
  \/ \E i \in 1..N :
      /\ pc[i] = "Backoff"
      /\ pc' = [pc EXCEPT ![i] = "Start"]
      /\ flag' = flag
      /\ announced' = announced
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ pc[i] = "EnterCS"
      /\ pc' = [pc EXCEPT ![i] = "InCS"]
      /\ flag' = flag
      /\ announced' = announced
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ pc[i] = "InCS"
      /\ pc' = [pc EXCEPT ![i] = "LeaveCS"]
      /\ flag' = flag
      /\ announced' = announced
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ pc[i] = "LeaveCS"
      /\ pc' = [pc EXCEPT ![i] = "Start"]
      /\ flag' = [flag EXCEPT ![i] = FALSE]
      /\ announced' = announced \ {i}
      /\ inCS' = inCS \ {i}

Spec ==
  Init /\ [][Next]_<<pc, flag, announced, inCS>>
  /\ WF_(pc, flag, announced, inCS)(\E i \in 1..N : pc[i] = "Start" /\ pc'[i] = "Announce")
  /\ SF_(pc, flag, announced, inCS)(\E i \in 1..N : pc[i] = "Announce" /\ pc'[i] = "EnterCS")

THEOREM Spec => []~(Cardinality(inCS) > 1)
THEOREM Spec => <>[](\E i \in 1..N : pc[i] = "InCS")
```