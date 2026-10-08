```
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc1, pc2, failed1, failed2

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc1 = "Noncritical"
  /\ pc2 = "Noncritical"
  /\ failed1 = FALSE
  /\ failed2 = [i \in 2..N |-> FALSE]

Next ==
  \/ (pc1 = "Noncritical" /\ x = 0 /\ y = 0 /\ b = FALSE
      /\ pc1' = "Waiting"
      /\ x' = 1
      /\ y' = 0
      /\ b' = FALSE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ (pc1 = "Waiting" /\ x = 1 /\ y = 0 /\ b = FALSE
      /\ pc1' = "Critical"
      /\ x' = 1
      /\ y' = 0
      /\ b' = TRUE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ (pc1 = "Critical" /\ x = 1 /\ y = 0 /\ b = TRUE
      /\ pc1' = "Noncritical"
      /\ x' = 0
      /\ y' = 0
      /\ b' = FALSE
      /\ UNCHANGED <<pc2, failed1, failed2>>)
  \/ \exists i \in 2..N :
      (pc2[i] = "Noncritical" /\ x = 0 /\ y = i
       /\ pc2' = [pc2 EXCEPT ![i] = "Waiting"]
       /\ x' = 0
       /\ y' = i
       /\ b' = FALSE
       /\ UNCHANGED <<pc1, failed1, failed2>>)
  \/ \exists i \in 2..N :
      (pc2[i] = "Waiting" /\ x = 0 /\ y = i /\ b = FALSE
       /\ pc2' = [pc2 EXCEPT ![i] = "Critical"]
       /\ x' = 0
       /\ y' = i
       /\ b' = TRUE
       /\ UNCHANGED <<pc1, failed1, failed2>>)
  \/ \exists i \in 2..N :
      (pc2[i] = "Critical" /\ x = 0 /\ y = i /\ b = TRUE
       /\ pc2' = [pc2 EXCEPT ![i] = "Noncritical"]
       /\ x' = 0
       /\ y' = i
       /\ b' = FALSE
       /\ UNCHANGED <<pc1, failed1, failed2>>)

MutualExclusion ==
  \A i, j \in 1..N :
    (pc1 = "Critical" \/ pc2[i] = "Critical") /\ (pc1 /= "Critical" \/ pc2[j] /= "Critical")

Spec ==
  Init /\ [][Next]_<<x, y, b, pc1, pc2, failed1, failed2>>
  /\ WF_vars(Next, <<pc1, pc2>>)
  /\ \A i \in 2..N : WF_vars(Next, <<pc2[i)>>)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]<>(\E i \in 1..N : (pc1 = "Critical" \/ pc2[i] = "Critical"))
```