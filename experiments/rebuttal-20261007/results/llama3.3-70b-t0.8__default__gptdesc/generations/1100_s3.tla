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
  \/ (pc1 = "ncl" /\ pc2 = "ncl" /\ locked = FALSE
      /\ pc1' = "l1" /\ pc2' = "ncl" /\ locked' = FALSE)
  \/ (pc1 = "ncl" /\ pc2 = "ncl" /\ locked = FALSE
      /\ pc1' = "ncl" /\ pc2' = "l2" /\ locked' = FALSE)
  \/ (pc1 = "l1" /\ locked = FALSE
      /\ pc1' = "cs" /\ pc2' = pc2 /\ locked' = TRUE)
  \/ (pc2 = "l2" /\ locked = FALSE
      /\ pc1' = pc1 /\ pc2' = "cs" /\ locked' = TRUE)
  \/ (pc1 = "cs"
      /\ pc1' = "ncl" /\ pc2' = pc2 /\ locked' = FALSE)
  \/ (pc2 = "cs"
      /\ pc1' = pc1 /\ pc2' = "ncl" /\ locked' = FALSE)

Spec == Init /\ [][Next]_<<pc1, pc2, locked>>
  
MutualExclusion ==
  <<pc1, pc2>> \in {[x \in {"ncl", "l1", "cs"}, y \in {"ncl", "l2", "cs"} :
                    ~(x = "cs" /\ y = "cs")]}

THEOREM Spec => []MutualExclusion

Liveness == <> (pc1 = "cs")

THEOREM Spec => WF_vars(Next, Liveness)
```