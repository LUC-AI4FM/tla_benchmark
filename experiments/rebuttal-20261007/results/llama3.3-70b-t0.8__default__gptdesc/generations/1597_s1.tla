```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc1, pc2, failed1, failed2

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc1 = "start"
  /\ pc2 = "start"
  /\ failed1 = FALSE
  /\ failed2 = [i \in 2..N |-> FALSE]

Next ==
  \/ (pc1 = "start" /\ x = 0 /\ y = 0)
    /\ (x' = 1) /\ (y' = y) /\ (b' = b) /\ (pc1' = "request") /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ (pc1 = "start" /\ x = 0 /\ y # 0)
    /\ (x' = x) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ (pc1 = "start" /\ x # 0)
    /\ (x' = x) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ (pc1 = "request")
    /\ (y # 0)
    /\ (x' = x) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ (pc1 = "request")
    /\ (y = 0)
    /\ (x' = x) /\ (y' = y + 1) /\ (b' = b) /\ (pc1' = "critical") /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ (pc1 = "critical")
    /\ (x' = x - 1) /\ (y' = y) /\ (b' = b) /\ (pc1' = "start") /\ (failed1' = failed1) /\ (failed2' = failed2)
  \/ \E i \in 2..N :
      ((pc2[i] = "start" /\ x = 0 /\ y # i)
        /\ (x' = 0) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = [j \in 2..N |-> IF j = i THEN "request" ELSE failed2[j]])
      )
    \/ ((pc2[i] = "start" /\ x # 0)
        /\ (x' = x) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = failed2)
      )
    \/ ((pc2[i] = "start" /\ x = 0 /\ y = i)
        /\ (x' = 1) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = [j \in 2..N |-> IF j = i THEN "request" ELSE failed2[j]])
      )
    \/ ((pc2[i] = "request")
        /\ (x # 0)
        /\ (x' = x) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = failed2)
      )
    \/ ((pc2[i] = "request")
        /\ (x = 0)
        /\ (x' = x) /\ (y' = y + i) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = [j \in 2..N |-> IF j = i THEN "critical" ELSE failed2[j]])
      )
    \/ ((pc2[i] = "critical")
        /\ (x' = x - 1) /\ (y' = y) /\ (b' = b) /\ (pc1' = pc1) /\ (failed1' = failed1) /\ (failed2' = [j \in 2..N |-> IF j = i THEN "start" ELSE failed2[j]])
      )

Spec ==
  /\ Init
  /\ [][Next]_x, y, b, pc1, pc2, failed1, failed2
  /\ WF_vars(Next, pc1)
  /\ \A i \in 2..N : WF_vars(Next, pc2[i])

THEOREM Spec => []<>(pc1 = "critical" \/ \E i \in 2..N : pc2[i] = "critical")
INVARIANT (pc1 = "critical") \/ (\E i \in 2..N : pc2[i] = "critical")
```