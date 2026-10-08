```
--------------------------- MODULE FastMutex2 ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, M
VARIABLE x, y, b, pc1, pc2, failure1, failure2, loopCount1, loopCount2

Spec == 
  ( /\ x = 0 
    /\ y = 0 
    /\ b = [i \in 1..N |-> FALSE]
    /\ pc1 = "Start"
    /\ pc2 = "Start"
    /\ failure1 = FALSE
    /\ failure2 = FALSE
    /\ loopCount1 = 0
    /\ loopCount2 = 0 )
  /\ [][Next]_<<x, y, b, pc1, pc2, failure1, failure2, loopCount1, loopCount2>>
  /\ WF_(Proc1(1))("InnerLoop")
  /\ WF_(Proc2(M+1))("InnerLoop")

Invariant == 
  ( \* Mutual exclusion
    ~EACH <<p, q>> \in (1..N) \X (1..N) : 
      ( p # q ) 
      /\ ( pc1[p] = "Critical" /\ failure1 = FALSE )
      /\ ( pc2[q] = "Critical" /\ failure2 = FALSE )
  )

Liveness == 
  <>[]<( \E i \in 1..N : 
    ( pc1[i] = "Critical" /\ failure1 = FALSE ) 
    \/ ( pc2[i] = "Critical" /\ failure2 = FALSE ) )>

Next == 
  ( \E self \in 1..M : Proc1(self) )
  \/ ( \E self \in (M+1)..N : Proc2(self) )

Proc1(self) == 
  ( pc1[self] = "Start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ y' = y
    /\ pc1' = [pc1 EXCEPT ![self] = "CheckY"]
    /\ failure1' = failure1
    /\ loopCount1' = [loopCount1 EXCEPT ![self] = loopCount1[self] + 1]
  )
  \/ ( pc1[self] = "CheckY"
      /\ y = 0
      /\ x' = x
      /\ y' = self
      /\ pc1' = [pc1 EXCEPT ![self] = "CheckX"]
      /\ failure1' = FALSE
      /\ loopCount1' = loopCount1
    )
  \/ ( pc1[self] = "CheckY"
      /\ y # 0
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc1' = [pc1 EXCEPT ![self] = "WaitY"]
      /\ failure1' = failure1
      /\ loopCount1' = loopCount1
    )
  \/ ( pc1[self] = "CheckX"
      /\ x # self
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc1' = [pc1 EXCEPT ![self] = "WaitAllB"]
      /\ failure1' = TRUE
      /\ loopCount1' = loopCount1
    )
  \/ ( pc1[self] = "CheckX"
      /\ x = self
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ pc1' = [pc1 EXCEPT ![self] = "Critical"]
      /\ failure1' = FALSE
      /\ loopCount1' = loopCount1
    )
  \/ ( pc1[self] = "WaitY"
      /\ y = 0
      /\ b' = [b EXCEPT ![self] = TRUE]
      /\ x' = self
      /\ y' = y
      /\ pc1' = [pc1 EXCEPT ![self] = "CheckY"]
      /\ failure1' = failure1
      /\ loopCount1' = [loopCount1 EXCEPT ![self] = loopCount1[self] + 1]
    )
  \/ ( pc1[self] = "WaitAllB"
      /\ \A j \in 1..N : ~b[j]
      /\ y # self
      /\ failure1' = TRUE
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc1' = [pc1 EXCEPT ![self] = "WaitY"]
      /\ loopCount1' = loopCount1
    )
  \/ ( pc1[self] = "Critical"
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = 0
      /\ pc1' = [pc1 EXCEPT ![self] = "Start"]
      /\ failure1' = FALSE
      /\ loopCount1' = loopCount1
    )

Proc2(self) == 
  ( pc2[self] = "Start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ y' = y
    /\ pc2' = [pc2 EXCEPT ![self] = "CheckY"]
    /\ failure2' = failure2
    /\ loopCount2' = [loopCount2 EXCEPT ![self] = loopCount2[self] + 1]
  )
  \/ ( pc2[self] = "CheckY"
      /\ y = 0
      /\ x' = x
      /\ y' = self
      /\ pc2' = [pc2 EXCEPT ![self] = "CheckX"]
      /\ failure2' = FALSE
      /\ loopCount2' = loopCount2
    )
  \/ ( pc2[self] = "CheckY"
      /\ y # 0
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc2' = [pc2 EXCEPT ![self] = "WaitY"]
      /\ failure2' = failure2
      /\ loopCount2' = loopCount2
    )
  \/ ( pc2[self] = "CheckX"
      /\ x # self
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc2' = [pc2 EXCEPT ![self] = "WaitAllB"]
      /\ failure2' = TRUE
      /\ loopCount2' = loopCount2
    )
  \/ ( pc2[self] = "CheckX"
      /\ x = self
      /\ b' = b
      /\ x' = x
      /\ y' = y
      /\ pc2' = [pc2 EXCEPT ![self] = "Critical"]
      /\ failure2' = FALSE
      /\ loopCount2' = loopCount2
    )
  \/ ( pc2[self] = "WaitY"
      /\ y = 0
      /\ b' = [b EXCEPT ![self] = TRUE]
      /\ x' = self
      /\ y' = y
      /\ pc2' = [pc2 EXCEPT ![self] = "CheckY"]
      /\ failure2' = failure2
      /\ loopCount2' = [loopCount2 EXCEPT ![self] = loopCount2[self] + 1]
    )
  \/ ( pc2[self] = "WaitAllB"
      /\ \A j \in 1..N : ~b[j]
      /\ y # self
      /\ failure2' = TRUE
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = y
      /\ pc2' = [pc2 EXCEPT ![self] = "WaitY"]
      /\ loopCount2' = loopCount2
    )
  \/ ( pc2[self] = "Critical"
      /\ b' = [b EXCEPT ![self] = FALSE]
      /\ x' = x
      /\ y' = 0
      /\ pc2' = [pc2 EXCEPT ![self] = "Start"]
      /\ failure2' = FALSE
      /\ loopCount2' = loopCount2
    )
```
Note: The `Proc1` and `Proc2` operators are identical except for the indexing, which is handled by the `self` variable. This could be refactored into a single operator with an additional parameter to handle the indexing difference between `Proc1` and `Proc2`. However, this would require changes to the model-checking configuration as well.