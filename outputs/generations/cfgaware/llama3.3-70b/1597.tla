--------------------------- MODULE FastMutualExclusion ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, pc1, pc2, failed1, failed2

Spec == 
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc1 = "Noncritical"
  /\ pc2 = [i \in 2..N |-> "Noncritical"]
  /\ failed1 = FALSE
  /\ failed2 = [i \in 2..N |-> FALSE]
  /\ [][Next]_<<x, y, b, pc1, pc2, failed1, failed2>>
  /\ WF_(<<x, y, b, pc1, pc2, failed1, failed2>>)(Next1)
  /\ \A i \in 2..N : WF_(<<x, y, b, pc1, pc2, failed1, failed2>>)(Next2(i))

Next == 
  (\E i \in {1} \cup (2..N) : Next1) \/ (\E i \in 2..N : Next2(i))

Next1 == 
  (pc1 = "Noncritical" /\ x' = 1 /\ pc1' = "Waiting" /\ y' = y /\ b' = b /\ pc2' = pc2 /\ failed1' = failed1 /\ failed2' = failed2)
  \/ (pc1 = "Waiting" /\ y = 0 /\ b = FALSE /\ x' = 0 /\ pc1' = "Critical" /\ y' = y /\ b' = b /\ pc2' = pc2 /\ failed1' = failed1 /\ failed2' = failed2)
  \/ (pc1 = "Waiting" /\ y > 0 /\ x' = 0 /\ pc1' = "Noncritical" /\ y' = y /\ b' = b /\ pc2' = pc2 /\ failed1' = failed1 /\ failed2' = failed2)
  \/ (pc1 = "Critical" /\ x' = 0 /\ pc1' = "Noncritical" /\ y' = y /\ b' = b /\ pc2' = pc2 /\ failed1' = failed1 /\ failed2' = failed2)

Next2(i) == 
  (pc2[i] = "Noncritical" /\ y' = i /\ pc2' = [pc2 EXCEPT ![i] = "Waiting"] /\ x' = x /\ b' = b /\ pc1' = pc1 /\ failed1' = failed1 /\ failed2' = [failed2 EXCEPT ![i] = FALSE])
  \/ (pc2[i] = "Waiting" /\ x = 0 /\ b = TRUE /\ y' = 0 /\ pc2' = [pc2 EXCEPT ![i] = "Critical"] /\ x' = x /\ b' = b /\ pc1' = pc1 /\ failed1' = failed1 /\ failed2' = failed2)
  \/ (pc2[i] = "Waiting" /\ x > 0 /\ y' = 0 /\ pc2' = [pc2 EXCEPT ![i] = "Noncritical"] /\ x' = x /\ b' = b /\ pc1' = pc1 /\ failed1' = failed1 /\ failed2' = failed2)
  \/ (pc2[i] = "Critical" /\ y' = 0 /\ pc2' = [pc2 EXCEPT ![i] = "Noncritical"] /\ x' = x /\ b' = b /\ pc1' = pc1 /\ failed1' = failed1 /\ failed2' = failed2)

Invariant == 
  \A i, j \in {1} \cup (2..N) : i # j => ~(pc1 = "Critical" /\ pc2[j] = "Critical")

Liveness == 
  <>[]<>(\E i \in {1} \cup (2..N) : (pc1 = "Critical") \/ (pc2[i] = "Critical"))
===============================================================================