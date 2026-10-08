------------------------------ MODULE MutualExclusion ------------------------------
CONSTANTS ProcSet

(* Lock states *)
CONSTANT Locked, Unlocked

(* Process control states *)
CONSTANT NC, TRY, CRIT, REL
StateSet == {NC, TRY, CRIT, REL}

VARIABLE lock, procState

Init ==
  /\ lock = Unlocked
  /\ procState \in [ProcSet -> StateSet]
  /\ \A p ∈ ProcSet : procState[p] = NC

Next ==
  ∃ p ∈ ProcSet :
    \/ (procState[p] = NC /\
        procState' = [procState EXCEPT ![p] = TRY] /\ lock' = lock)
    \/ (procState[p] = TRY /\ lock = Unlocked /\
        procState' = [procState EXCEPT ![p] = CRIT] /\ lock' = Locked)
    \/ (procState[p] = CRIT /\
        procState' = [procState EXCEPT ![p] = REL] /\ lock' = lock)
    \/ (procState[p] = REL /\
        procState' = [procState EXCEPT ![p] = NC] /\ lock' = Unlocked)

TypeOK ==
  /\ lock ∈ {Locked, Unlocked}
  /\ procState \in [ProcSet -> StateSet]

LockInv ==
  LET holding == {p ∈ ProcSet : procState[p] = CRIT \/ procState[p] = REL} IN
    (holding # {} => lock = Locked)
    /\ (holding = {} => lock = Unlocked)

Spec == Init /\ [][Next]_(lock,procState)

MutualExcl ==
  \A p1, p2 ∈ ProcSet : (p1 # p2) => ~(procState[p1] = CRIT /\ procState[p2] = CRIT)

THEOREM Spec => []TypeOK
THEOREM Spec => []LockInv
THEOREM Spec => []MutualExcl

=============================================================================