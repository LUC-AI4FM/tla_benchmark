MODULE MutualExclusionLock

EXTENDS Naturals, TLC

CONSTANTS ProcSet

VARIABLE lock, procState

(* Type invariants *)
TypeInv == lock ∈ {TRUE, FALSE} 
          /\ \A p ∈ ProcSet : procState[p] ∈ {"NC","TRY","CS","REL"}

(* Mutual exclusion invariant *)
MutualExcl == \A p,q ∈ ProcSet : (p # q) => ~(procState[p]="CS" /\ procState[q]="CS")

(* Lock consistency invariant *)
LockConsistent == 
  (Exists p ∈ ProcSet : procState[p] = "CS" \/ procState[p] = "REL") => lock = TRUE
  /\ lock = TRUE => Exists p ∈ ProcSet : procState[p] = "CS" \/ procState[p] = "REL"

(* Initial condition *)
Init == 
  /\ lock = FALSE
  /\ \A p ∈ ProcSet : procState[p] = "NC"

(* Next-state relation *)
Next ==
  \E p ∈ ProcSet :
    (procState[p] = "NC" 
     /\ procState' = [procState EXCEPT ![p] = "TRY"]
     /\ UNCHANGED <<lock>>)
   \/ (procState[p] = "TRY" 
       /\ lock = FALSE
       /\ procState' = [procState EXCEPT ![p] = "CS"]
       /\ lock' = TRUE)
   \/ (procState[p] = "CS"
       /\ procState' = [procState EXCEPT ![p] = "REL"]
       /\ UNCHANGED <<lock>>)
   \/ (procState[p] = "REL"
       /\ procState' = [procState EXCEPT ![p] = "NC"]
       /\ lock' = FALSE)

(* Specification *)
Spec == Init /\ [][Next]_<<lock,procState>>

(* Combined invariant for proof obligations *)
Inv == TypeInv /\ MutualExcl /\ LockConsistent

THEOREM Spec => []Inv

END MODULE