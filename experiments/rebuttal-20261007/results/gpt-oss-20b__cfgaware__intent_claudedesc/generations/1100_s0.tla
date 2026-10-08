------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS TLC

VARIABLES lock, pc1, pc2

(* Initial state *)
Init == 
  /\ lock = 0
  /\ pc1 = "NC"
  /\ pc2 = "NC"

(* Actions for process 1 *)
NC1 == 
  /\ pc1 = "NC"
  /\ pc1' = "ACQ"

ACQ1 ==
  /\ pc1 = "ACQ"
  /\ lock = 0
  /\ lock' = 1
  /\ pc1' = "CRIT"

CRIT1 ==
  /\ pc1 = "CRIT"
  /\ pc1' = "POST"

POST1 ==
  /\ pc1 = "POST"
  /\ lock = 1
  /\ lock' = 0
  /\ pc1' = "NC"

(* Actions for process 2 *)
NC2 == 
  /\ pc2 = "NC"
  /\ pc2' = "ACQ"

ACQ2 ==
  /\ pc2 = "ACQ"
  /\ lock = 0
  /\ lock' = 1
  /\ pc2' = "CRIT"

CRIT2 ==
  /\ pc2 = "CRIT"
  /\ pc2' = "POST"

POST2 ==
  /\ pc2 = "POST"
  /\ lock = 1
  /\ lock' = 0
  /\ pc2' = "NC"

(* Next-state relation *)
Next == 
  \/ NC1 \/ ACQ1 \/ CRIT1 \/ POST1
  \/ NC2 \/ ACQ2 \/ CRIT2 \/ POST2

Spec == Init /\ [][Next]_<<lock, pc1, pc2>>

(* Type correctness invariant *)
TypeOK ==
  /\ lock ∈ {0, 1}
  /\ pc1 ∈ {"NC","ACQ","CRIT","POST"}
  /\ pc2 ∈ {"NC","ACQ","CRIT","POST"}

(* Mutual-exclusion invariant *)
LockInv ==
  /\ ~( (pc1 ∈ {"CRIT","POST"}) /\ (pc2 ∈ {"CRIT","POST"}) )
  /\ (lock = 0 <=> pc1 # "CRIT" /\ pc1 # "POST" /\ pc2 # "CRIT" /\ pc2 # "POST")
  /\ (lock = 1 <=> ((pc1 ∈ {"CRIT","POST"}) \/ (pc2 ∈ {"CRIT","POST"})) )

(* Theorems *)
THEOREM TypeOK_I: Spec => []TypeOK
  PROOF
    BY WF_vars, Init, Next, TypeOK
  QED

THEOREM LockInv_I: Spec => []LockInv
  PROOF
    BY WF_vars, Init, Next, LockInv
  QED

=============================================================================