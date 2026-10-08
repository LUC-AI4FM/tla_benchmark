------------------------------ MODULE AtomicCommit ------------------------------
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------------*)
(* Constants *)
CONSTANTS RM, r2          \* RM is the set of resource managers.
                           \* r2 is a distinguished manager (unused in the spec).

(*--------------------------------------------------------------------------*)
(* State space *)
StateSet == {"working", "prepared", "committed", "aborted"}

VARIABLE state

(*--------------------------------------------------------------------------*)
(* Initial condition: all RMs start working *)
Init ==
  \A r \in RM : state[r] = "working"

(*--------------------------------------------------------------------------*)
(* Actions *)

Prepare(r) ==
  /\ r \in RM
  /\ state[r] = "working"
  /\ state' = [state EXCEPT ![r] = "prepared"]

Abort(r) ==
  /\ r \in RM
  /\ state[r] \in {"working", "prepared"}
  /\ state' = [state EXCEPT ![r] = "aborted"]

Commit(r) ==
  /\ r \in RM
  /\ state[r] = "prepared"
  /\ \A r' \in RM : state[r'] \in {"prepared", "committed"}
  /\ state' = [state EXCEPT ![r] = "committed"]

(*--------------------------------------------------------------------------*)
(* Next-state relation *)
Next ==
  \/ \E r \in RM: Prepare(r)
  \/ \E r \in RM: Abort(r)
  \/ \E r \in RM: Commit(r)

(*--------------------------------------------------------------------------*)
(* Specification *)
TCSpec == Init /\ [][Next]_state

(*--------------------------------------------------------------------------*)
(* Invariants *)

TCTypeOK ==
  \A r \in RM : state[r] \in StateSet

TCConsistent ==
  \A r1, r2' \in RM :
    ~(state[r1] = "committed" /\ state[r2'] = "aborted")

=============================================================================