------------------------------ MODULE SimpleConcurrent ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS MaxReg, UnchangedVals

VARIABLES reg, unchanged

(* --------------------------------------------------------------------------- *)
(* Initial state: each component is within its finite domain.                  *)
Init == 
  /\ reg \in 0..MaxReg
  /\ unchanged \in UnchangedVals

(* --------------------------------------------------------------------------- *)
(* Increment action: increments the regularly-updated component while leaving   *)
(* the unchanged component stable.                                            *)
Increment ==
  /\ reg < MaxReg
  /\ UNCHANGED unchanged
  /\ reg' = reg + 1

Next == Increment

(* --------------------------------------------------------------------------- *)
(* Invariants: domain membership and stability of the unchanged component.    *)
DomainInvariant == 
  /\ reg \in 0..MaxReg
  /\ unchanged \in UnchangedVals

UnchangedInvariant ==
  /\ (reg < MaxReg) => (unchanged' = unchanged)

(* The externally supplied constant is a CONSTANT; it never changes.          *)
ConstInvariant == TRUE

(* --------------------------------------------------------------------------- *)
(* Specification: initialization, next-state relation, and fairness to ensure *)
(* progress until the termination condition is reached.                       *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

=============================================================================