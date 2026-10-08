```
MODULE FastMutex
EXTENDS Integers

CONSTANTS M, N

VARIABLES x, y, b, pc1, pc2, inCS

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc1 = [i \in 1..M |-> "NonCritical"]
  /\ pc2 = [i \in (M+1)..N |-> "NonCritical"]
  /\ inCS = {}

Next ==
  \/ (\E i \in 1..M : 
        pc1[i] = "NonCritical" 
        /\ x = 0 
        /\ y = 0 
        /\ pc1' = [pc1 EXCEPT ![i] = "TryEnter"]
        /\ UNCHANGED <<x, y, b, pc2, inCS>>)
  \/ (\E i \in 1..M : 
        pc1[i] = "TryEnter" 
        /\ x = 0 
        /\ pc1' = [pc1 EXCEPT ![i] = "EnterCS"]
        /\ x' = i
        /\ UNCHANGED <<y, b, pc2, inCS>>)
  \/ (\E i \in 1..M : 
        pc1[i] = "EnterCS" 
        /\ (x = i /\ y /= i) 
        /\ b' = TRUE
        /\ pc1' = [pc1 EXCEPT ![i] = "Critical"]
        /\ inCS' = inCS \cup {i}
        /\ UNCHANGED <<x, y>>)
  \/ (\E i \in 1..M : 
        pc1[i] = "Critical" 
        /\ b 
        /\ pc1' = [pc1 EXCEPT ![i] = "ExitCS"]
        /\ UNCHANGED <<x, y, b, pc2, inCS>>)
  \/ (\E i \in 1..M : 
        pc1[i] = "ExitCS" 
        /\ x = i
        /\ pc1' = [pc1 EXCEPT ![i] = "NonCritical"]
        /\ x' = 0
        /\ b' = FALSE
        /\ inCS' = inCS \ {i}
        /\ UNCHANGED <<y>>)
  \/ (\E i \in (M+1)..N : 
        pc2[i] = "NonCritical" 
        /\ x = 0 
        /\ y = 0 
        /\ pc2' = [pc2 EXCEPT ![i] = "TryEnter"]
        /\ UNCHANGED <<x, y, b, pc1, inCS>>)
  \/ (\E i \in (M+1)..N : 
        pc2[i] = "TryEnter" 
        /\ x = 0 
        /\ pc2' = [pc2 EXCEPT ![i] = "EnterCS"]
        /\ y' = i
        /\ UNCHANGED <<x, b, pc1, inCS>>)
  \/ (\E i \in (M+1)..N : 
        pc2[i] = "EnterCS" 
        /\ (y = i /\ x /= i) 
        /\ b' = TRUE
        /\ pc2' = [pc2 EXCEPT ![i] = "Critical"]
        /\ inCS' = inCS \cup {i}
        /\ UNCHANGED <<x, y>>)
  \/ (\E i \in (M+1)..N : 
        pc2[i] = "Critical" 
        /\ b 
        /\ pc2' = [pc2 EXCEPT ![i] = "ExitCS"]
        /\ UNCHANGED <<x, y, b, pc1, inCS>>)
  \/ (\E i \in (M+1)..N : 
        pc2[i] = "ExitCS" 
        /\ y = i
        /\ pc2' = [pc2 EXCEPT ![i] = "NonCritical"]
        /\ y' = 0
        /\ b' = FALSE
        /\ inCS' = inCS \ {i}
        /\ UNCHANGED <<x>>)

Spec == Init /\ [][Next]_<<x, y, b, pc1, pc2, inCS>>
           /\ WF_vars(<<pc1, pc2>>)
           /\ SF_vars(<<pc1, pc2>>)

MutualExclusion == [](Cardinality(inCS) <= 1)

Liveness == <>[]<>(\E i \in 1..N : pc1[i] = "Critical" \/ pc2[i] = "Critical")
```