MODULE TwoProcessMutex
EXTENDS TLC

CONSTANTS ProcSet

VARIABLES pc, lockOwner

(* Type invariants *)
TypeInv == /\ pc \in [ProcSet -> {"nc", "l1", "cs"}]
          /\ lockOwner \in ProcSet \/ {0}

Init ==
    /\ pc[1] = "nc"
    /\ pc[2] = "nc"
    /\ lockOwner = 0

Next ==
    \E i \in ProcSet :
        \/ (pc[i] = "nc" /\
            pc' = [pc EXCEPT ![i] = IF i=1 THEN "l1" ELSE "l2"] /\
            lockOwner' = lockOwner)
        \/ (((i = 1) /\ pc[i] = "l1") \/ ((i = 2) /\ pc[i] = "l2")) /\
           lockOwner = 0 /\
           pc' = [pc EXCEPT ![i] = "cs"] /\
           lockOwner' = i
        \/ (pc[i] = "cs" /\
            pc' = [pc EXCEPT ![i] = "nc"] /\
            lockOwner' = 0)

MutualExcl == \A i,j \in ProcSet : i /= j => ~(pc[i]="cs" /\ pc[j]="cs")

LockCorrect ==
    IF lockOwner = 0 THEN
        \A i \in ProcSet : pc[i] # "cs"
    ELSE
        \A i \in ProcSet : (pc[i]="cs") <=> (i = lockOwner)

Invariant == TypeInv /\ MutualExcl /\ LockCorrect

LivenessProp == [] (pc[1] = "l1" -> <> (pc[1] = "cs"))

Spec == Init /\ [][Next]_<<pc, lockOwner>> /\ Invariant /\ LivenessProp