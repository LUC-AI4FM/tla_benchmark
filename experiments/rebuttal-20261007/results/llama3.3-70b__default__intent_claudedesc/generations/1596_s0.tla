```
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N, M
VARIABLES flag, fastPathVar1, fastPathVar2, pc

Init ==
  /\ flag = [i \in 1..N |-> FALSE]
  /\ fastPathVar1 = 0
  /\ fastPathVar2 = 0
  /\ pc = [i \in 1..N |-> "start"]

Next ==
  \/ \E i \in 1..M : NextProcess(i)
  \/ \E i \in (M+1)..N : NextProcess(i)

NextProcess(i) ==
  pc[i] = "start" /\ flag[i] = FALSE /\ fastPathVar1 = 0
  /\ (pc' = [pc EXCEPT ![i] = "trying"]
      /\ flag' = [flag EXCEPT ![i] = TRUE]
      /\ UNCHANGED <<fastPathVar1, fastPathVar2>>)
  \/ pc[i] = "start" /\ flag[i] = FALSE /\ fastPathVar1 # 0
  /\ (pc' = [pc EXCEPT ![i] = "backoff"]
      /\ UNCHANGED <<flag, fastPathVar1, fastPathVar2>>)
  \/ pc[i] = "trying"
  /\ (fastPathVar2 = 0
      /\ (pc' = [pc EXCEPT ![i] = "critical"]
          /\ fastPathVar2' = i
          /\ UNCHANGED <<flag, fastPathVar1>>)
      \/ fastPathVar2 # 0
      /\ (pc' = [pc EXCEPT ![i] = "backoff"]
          /\ UNCHANGED <<flag, fastPathVar1, fastPathVar2>>))
  \/ pc[i] = "critical"
  /\ (pc' = [pc EXCEPT ![i] = "end"]
      /\ flag' = [flag EXCEPT ![i] = FALSE]
      /\ fastPathVar2' = 0
      /\ UNCHANGED fastPathVar1)
  \/ pc[i] = "backoff" /\ fastPathVar1 = 0
  /\ (pc' = [pc EXCEPT ![i] = "trying"]
      /\ UNCHANGED <<flag, fastPathVar1, fastPathVar2>>)

Spec ==
  Init /\ [][Next]_<<flag, fastPathVar1, fastPathVar2, pc>>
  /\ WF_vars(NextProcess)(1..M)
  /\ WF_vars(NextProcess)(M+1..N)

MutualExclusion ==
  \A i, j \in 1..N : pc[i] = "critical" /\ pc[j] = "critical" => i = j

Liveness ==
  <> \E i \in 1..N : pc[i] = "critical"

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
```