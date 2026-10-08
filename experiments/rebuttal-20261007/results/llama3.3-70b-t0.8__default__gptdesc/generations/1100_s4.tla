```
MODULE MutualExclusionLock
EXTENDS Integers

CONSTANTS P1, P2
VARIABLES pc1, pc2, locked

Init ==
  /\ pc1 = "ncl" 
  /\ pc2 = "ncl"
  /\ locked = FALSE

Next ==
  \/ (pc1 = "ncl" /\ locked = FALSE /\ pc1' = "l1" /\ pc2' = pc2 /\ locked' = FALSE)
  \/ (pc1 = "l1" /\ locked = FALSE /\ pc1' = "cs" /\ pc2' = pc2 /\ locked' = TRUE)
  \/ (pc1 = "cs" /\ locked = TRUE /\ pc1' = "ncl" /\ pc2' = pc2 /\ locked' = FALSE)
  \/ (pc2 = "ncl" /\ locked = FALSE /\ pc2' = "l1" /\ pc1' = pc1 /\ locked' = FALSE)
  \/ (pc2 = "l1" /\ locked = FALSE /\ pc2' = "cs" /\ pc1' = pc1 /\ locked' = TRUE)
  \/ (pc2 = "cs" /\ locked = TRUE /\ pc2' = "ncl" /\ pc1' = pc1 /\ locked' = FALSE)
  \/ (pc1' = pc1 /\ pc2' = pc2 /\ locked' = locked)

Spec == Init /\ [][Next]_<<pc1, pc2, locked>>
MutualExclusion == (pc1 \in {"cs"} /\ pc2 \in {"cs"}) => FALSE

THEOREM Spec => []MutualExclusion
THEOREM Spec => <><pc1 = "l1"> => <>pc1 = "cs"
```
Note: The above TLA+ code models the behavior of two processes trying to access a critical section using a mutual exclusion lock. It defines an invariant `MutualExclusion` that ensures at most one process can be in the critical section, and it also includes a liveness property ensuring that if Process 1 reaches the waiting location "l1", it will eventually reach the critical-section location "cs".