```
---------------------------- MODULE FastMutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE x, y, b, j

Invariant == \A i, k \in 1..N : i # k => ~(b[i] /\ b[k])

CondLiveness == 
  <>[]<>(\E i \in 1..N : b[i]) \/ 
  [](~(\E i \in 1..N : ~b[i]) => <>(\E i \in 1..N : b[i]))

FairSpec == 
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ j = [i \in 1..N |-> 0]
  /\ [][
      (\E i \in 1..N : 
        /\ b[i] = FALSE
        /\ b' = [b EXCEPT ![i] = TRUE]
        /\ x' = i
        /\ y' = y
        /\ j' = [j EXCEPT ![i] = 0]
      )
      \/ 
      (\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x = i
        /\ y = 0
        /\ y' = i
        /\ x' = x
        /\ b' = b
        /\ j' = [j EXCEPT ![i] = 1]
      )
      \/ 
      (\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x = i
        /\ y = i
        /\ x' = x
        /\ y' = y
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ j' = [j EXCEPT ![i] = 2]
      )
      \/ 
      (\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x # i
        /\ y' = y
        /\ x' = x
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ j' = [j EXCEPT ![i] = 3]
      )
      \/ 
      (\E i \in 1..N : 
        /\ b[i] = FALSE
        /\ y # 0
        /\ y' = 0
        /\ x' = x
        /\ b' = b
        /\ j' = [j EXCEPT ![i] = 4]
      )
    ]
    /\ WF_VAR([][(\E i \in 1..N : 
        /\ b[i] = FALSE
        /\ b' = [b EXCEPT ![i] = TRUE]
        /\ x' = i
        /\ y' = y
        /\ j' = [j EXCEPT ![i] = 0]
      )], <<x, y, b, j>>)
    /\ WF_VAR([][(\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x = i
        /\ y = 0
        /\ y' = i
        /\ x' = x
        /\ b' = b
        /\ j' = [j EXCEPT ![i] = 1]
      )], <<x, y, b, j>>)
    /\ WF_VAR([][(\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x = i
        /\ y = i
        /\ x' = x
        /\ y' = y
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ j' = [j EXCEPT ![i] = 2]
      )], <<x, y, b, j>>)
    /\ WF_VAR([][(\E i \in 1..N : 
        /\ b[i] = TRUE
        /\ x # i
        /\ y' = y
        /\ x' = x
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ j' = [j EXCEPT ![i] = 3]
      )], <<x, y, b, j>>)
    /\ WF_VAR([][(\E i \in 1..N : 
        /\ b[i] = FALSE
        /\ y # 0
        /\ y' = 0
        /\ x' = x
        /\ b' = b
        /\ j' = [j EXCEPT ![i] = 4]
      )], <<x, y, b, j>>)
```
Note: The `WF_VAR` operator is used to specify weak fairness for each process. This ensures that if a process is enabled infinitely often, it will eventually take a step.