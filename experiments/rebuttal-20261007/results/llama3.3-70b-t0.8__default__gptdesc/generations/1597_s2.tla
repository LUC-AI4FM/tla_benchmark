```
MODULE LamportFastMutualExclusion
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES x, y, b, pc1, pc2, failed1, failed2

Init == 
  (x = 0) ∧ (y = 0) ∧ (b = FALSE) ∧ 
  (pc1 = "Start") ∧ 
  (pc2 = [i \in 2..N |-> "Start"]) ∧ 
  (failed1 = FALSE) ∧ 
  (failed2 = [i \in 2..N |-> FALSE])

Next == 
  /\ (IF pc1 = "Start" THEN 
        /\ x = 1
        /\ pc1 = "Request"
      ELSE IF pc1 = "Request" THEN 
        /\ y = 1
        /\ b = TRUE
        /\ pc1 = "Waiting"
      ELSE IF pc1 = "Waiting" THEN 
        /\ (y = 0) ∨ (b = FALSE)
        /\ pc1 = "Critical"
      ELSE IF pc1 = "Critical" THEN 
        /\ x = 0
        /\ y = 0
        /\ b = FALSE
        /\ pc1 = "Start")
  /\ \A i \in 2..N [ 
      IF pc2[i] = "Start" THEN 
        /\ x = 1
        /\ pc2[i] = "Request"
      ELSE IF pc2[i] = "Request" THEN 
        /\ y = 1
        /\ b = TRUE
        /\ pc2[i] = "Waiting"
      ELSE IF pc2[i] = "Waiting" THEN 
        /\ (y = 0) ∨ (b = FALSE)
        /\ pc2[i] = "Critical"
      ELSE IF pc2[i] = "Critical" THEN 
        /\ x = 0
        /\ y = 0
        /\ b = FALSE
        /\ pc2[i] = "Start"]
  /\ failed1' = failed1
  /\ failed2' = [i \in 2..N |-> failed2[i]]

Spec == Init ∧ [][Next]_x ∧ WF1(Next) ∧ SF1(Next) ∧ WF2(Next) ∧ SF2(Next)

MutualExclusionInvariant == 
  \A i, j \in 1..N : 
    (pc1 = "Critical") ∧ (pc2[j] = "Critical") ⇒ (i = j)

LivenessProperty == 
  <>[]\E i \in 1..N : pc1 = "Critical" ∨ pc2[i] = "Critical"

THEOREM Spec => []MutualExclusionInvariant
THEOREM Spec => LivenessProperty

WF1(Next) == 
  \A p \in {1} [][Next]_<<pc1, x, y, b>> 

SF1(Next) == 
  \A p \in {1} <><<pc1 = "Start">>_<<<pc1, x, y, b>>> 

WF2(Next) == 
  \A i \in 2..N [][Next]_<<pc2[i], x, y, b>> 

SF2(Next) == 
  \A i \in 2..N <><<pc2[i] = "Start">>_<<<pc2[i], x, y, b>>> 
```