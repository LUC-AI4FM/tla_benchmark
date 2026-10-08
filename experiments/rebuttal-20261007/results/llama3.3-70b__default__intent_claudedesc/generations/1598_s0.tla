```
MODULE MutualExclusion
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N
VARIABLES x, y, b, cs

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = {}

Next ==
  \/ \E i \in 1..N :
      /\ ~ (i \in cs)
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ x' = i
      /\ y' = i
      /\ UNCHANGED cs
  \/ \E i \in 1..N :
      /\ b[i]
      /\ x = i
      /\ y /= i
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ UNCHANGED x
      /\ UNCHANGED y
      /\ UNCHANGED cs
  \/ \E i \in 1..N :
      /\ b[i]
      /\ x = i
      /\ y = i
      /\ cs' = cs \cup {i}
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ UNCHANGED x
      /\ y' = 0
  \/ \E i \in 1..N :
      /\ i \in cs
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ x' = 0
      /\ y' = 0
      /\ cs' = cs \ {i}
  \/ \E i \in 1..N :
      /\ ~ (i \in cs)
      /\ b[i]
      /\ y /= 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ UNCHANGED x
      /\ UNCHANGED y
      /\ UNCHANGED cs

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, cs>>
  /\ WF_(Next, <<x, y, b, cs>>)

THEOREM Spec => []~(EXISTS <<i, j>> \in (1..N \X 1..N) : i /= j /\ {i, j} \subseteq cs)
THEOREM Spec => <>[]<<cs /= {}>>
```