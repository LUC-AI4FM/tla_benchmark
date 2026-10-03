---------------- MODULE Barrier ----------------
EXTENDS Integers

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc

ProcSet == 1..N

vars == <<pc>>

-----------------------------------------------------------------------------
(*
 The state of a process is either "b0" (before the barrier) or "b1" (at the
 barrier).
*)

(* The type correctness invariant for the state variables. *)
TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

(* The initial state predicate: all processes start in state "b0". *)
Init == pc = [p \in ProcSet |-> "b0"]

(* A single process `p` moves from "b0" to "b1". *)
EnterBarrier(p) ==
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

(* When all processes are at "b1", the barrier resets them all to "b0" simultaneously. *)
ResetBarrier ==
    /\ \A p \in ProcSet : pc[p] = "b1"
    /\ pc' = [p \in ProcSet |-> "b0"]

(* The next-state relation for the system. *)
Next ==
    \/ \E p \in ProcSet : EnterBarrier(p)
    \/ ResetBarrier

-----------------------------------------------------------------------------

(*
 The main specification, including safety and liveness.
 Weak fairness on each `EnterBarrier` action ensures that no process is
 infinitely delayed from entering the barrier. Weak fairness on the
 `ResetBarrier` action ensures that the barrier eventually resets when all
 processes are ready.
*)
Spec == Init /\ [][Next]_vars
           /\ (\A p \in ProcSet : WF_vars(EnterBarrier(p)))
           /\ WF_vars(ResetBarrier)

-----------------------------------------------------------------------------
(* PROPERTIES *)

(*
 The temporal barrier property: a process cannot leave the barrier (transition
 from "b1" to "b0") while some other process has not yet entered it (is still
 in "b0"). This is a safety property of the protocol.
*)
BarrierProperty ==
    [](\A p, q \in ProcSet : (pc[p] = "b1" /\ pc'[p] = "b0") => pc[q] = "b1")

(* It should be a theorem that the specification implies the properties. *)
THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty

=============================================================================