```
MODULE FastMutex2
EXTENDS Integers, FiniteSets

CONSTANTS N, M
VARIABLES x, y, b, loopCount1, loopCount2, failure1, failure2, pc1, pc2

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ loopCount1 = 0
  /\ loopCount2 = 0
  /\ failure1 = FALSE
  /\ failure2 = FALSE
  /\ pc1 = "Start"
  /\ pc2 = "Start"

Next ==
  \/ (pc1 = "Start" /\ b[1] = FALSE /\ x = 0 /\ y = 0
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ x' = 1
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "CheckY")
  \/ (pc1 = "Start" /\ b[1] = FALSE /\ x = 0 /\ y # 0
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ x' = 1
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "WaitY")
  \/ (pc1 = "CheckY" /\ y # 0
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "Start")
  \/ (pc1 = "CheckY" /\ y = 0
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ x' = x
      /\ y' = 1
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "CheckX")
  \/ (pc1 = "CheckX" /\ x # 1
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = TRUE
      /\ pc1' = "WaitB")
  \/ (pc1 = "CheckX" /\ x = 1 /\ failure1 = FALSE
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "CS")
  \/ (pc1 = "WaitB" /\ \A i \in 1..N : ~b[i]
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "CheckY2")
  \/ (pc1 = "WaitB" /\ \E i \in 1..N : b[i]
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "WaitB")
  \/ (pc1 = "CheckY2" /\ y # 1
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = TRUE
      /\ pc1' = "Start")
  \/ (pc1 = "CheckY2" /\ y = 1
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "Start")
  \/ (pc1 = "CS" /\ b[1] = TRUE
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ x' = x
      /\ y' = 0
      /\ loopCount1' = loopCount1 + 1
      /\ failure1' = failure1
      /\ pc1' = "Start")
  \/ (pc2 = "Start" /\ b[2] = FALSE /\ x = 0 /\ y = 0
      /\ b' = [b EXCEPT ![2] = TRUE]
      /\ x' = 2
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "CheckY")
  \/ (pc2 = "Start" /\ b[2] = FALSE /\ x = 0 /\ y # 0
      /\ b' = [b EXCEPT ![2] = TRUE]
      /\ x' = 2
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "WaitY")
  \/ (pc2 = "CheckY" /\ y # 0
      /\ b' = [b EXCEPT ![2] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "Start")
  \/ (pc2 = "CheckY" /\ y = 0
      /\ b' = [b EXCEPT ![2] = TRUE]
      /\ x' = x
      /\ y' = 2
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "CheckX")
  \/ (pc2 = "CheckX" /\ x # 2
      /\ b' = [b EXCEPT ![2] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = TRUE
      /\ pc2' = "WaitB")
  \/ (pc2 = "CheckX" /\ x = 2 /\ failure2 = FALSE
      /\ b' = [b EXCEPT ![2] = TRUE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "CS")
  \/ (pc2 = "WaitB" /\ \A i \in 1..N : ~b[i]
      /\ b' = [b EXCEPT ![2] = TRUE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "CheckY2")
  \/ (pc2 = "WaitB" /\ \E i \in 1..N : b[i]
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "WaitB")
  \/ (pc2 = "CheckY2" /\ y # 2
      /\ b' = [b EXCEPT ![2] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = TRUE
      /\ pc2' = "Start")
  \/ (pc2 = "CheckY2" /\ y = 2
      /\ b' = [b EXCEPT ![2] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "Start")
  \/ (pc2 = "CS" /\ b[2] = TRUE
      /\ b' = [b EXCEPT ![2] = FALSE]
      /\ x' = x
      /\ y' = 0
      /\ loopCount2' = loopCount2 + 1
      /\ failure2' = failure2
      /\ pc2' = "Start")

Spec ==
  Init /\ [][Next]_<<x, y, b, loopCount1, loopCount2, failure1, failure2, pc1, pc2>>
  /\ WF_vars(Next, <<pc1, pc2>>)

THEOREM Spec => []<>(pc1 = "CS" \/ pc2 = "CS")
```