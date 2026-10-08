```
MODULE FastMutex
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES flag, reg1, reg2, cs

Init ==
  /\ flag = [i \in 1..N |-> FALSE]
  /\ reg1 = 0
  /\ reg2 = 0
  /\ cs = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
    /\ ~cs[i]
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ reg1' = reg1
    /\ reg2' = reg2
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ flag[i]
    /\ reg1 = 0
    /\ reg1' = i
    /\ reg2' = reg2
    /\ flag' = flag
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ flag[i]
    /\ reg1 = i
    /\ reg2 = 0
    /\ reg2' = i
    /\ reg1' = reg1
    /\ flag' = flag
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ flag[i]
    /\ reg1 = i
    /\ reg2 = i
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ reg1' = reg1
    /\ reg2' = reg2
    /\ flag' = flag
  \/ \E i \in 1..N :
    /\ cs[i]
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ reg1' = 0
    /\ reg2' = 0
    /\ flag' = [flag EXCEPT ![i] = FALSE]

Spec ==
  Init /\ [][Next]_<<flag, reg1, reg2, cs>>
  /\ WF_(\E i \in 1..N : ~cs[i] /\ flag' = [flag EXCEPT ![i] = TRUE])_<<flag, reg1, reg2, cs>>
  /\ WF_(\E i \in 1..N : flag[i] /\ reg1 = 0 /\ reg1' = i)_<<flag, reg1, reg2, cs>>
  /\ WF_(\E i \in 1..N : flag[i] /\ reg1 = i /\ reg2 = 0 /\ reg2' = i)_<<flag, reg1, reg2, cs>>
  /\ WF_(\E i \in 1..N : flag[i] /\ reg1 = i /\ reg2 = i /\ cs' = [cs EXCEPT ![i] = TRUE])_<<flag, reg1, reg2, cs>>
  /\ WF_(\E i \in 1..N : cs[i] /\ cs' = [cs EXCEPT ![i] = FALSE] /\ reg1' = 0 /\ reg2' = 0)_<<flag, reg1, reg2, cs>>

THEOREM Spec => []~(\E i, j \in 1..N : i # j /\ cs[i] /\ cs[j])
```