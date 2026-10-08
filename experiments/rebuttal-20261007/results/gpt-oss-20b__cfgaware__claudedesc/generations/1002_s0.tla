------------------------------ MODULE CyclicBarrier ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLE pc

(* --------------------------------------------------------------------------- *)
(* Initial state: every process starts at the first barrier location "b0"       *)
Init == pc = [i \in 1..N |-> "b0"]

(* --------------------------------------------------------------------------- *)
(* Action for an individual process i arriving at the barrier.                 *)
b0(i) ==
    /\ i \in 1..N
    /\ pc[i] = "b0"
    /\ pc' = [pc EXCEPT ![i] = "b1"]

(* --------------------------------------------------------------------------- *)
(* Barrier release: fires only when all processes are at "b1".                *)
b1 ==
    /\ \A i \in 1..N : pc[i] = "b1"
    /\ pc' = [pc EXCEPT ![*] = "b0"]

(* --------------------------------------------------------------------------- *)
(* Next-state relation: any process may perform b0, or the barrier may release. *)
Next == \E i \in 1..N : (b0(i) \/ b1)

(* --------------------------------------------------------------------------- *)
(* Temporal specification of the system.                                       *)
Spec == Init /\ [][Next]_pc

(* --------------------------------------------------------------------------- *)
(* Type invariant: pc always maps each process to a valid location.           *)
TypeOK ==
    \A i \in 1..N : pc[i] \in {"b0", "b1"}

(* --------------------------------------------------------------------------- *)
(* Safety property: no process that has passed the barrier may leave it while
   another process is still at the first location.                            *)
BarrierProperty ==
    \A i, j \in 1..N :
        (pc[i] = "b0" /\ pc[j] = "b1") => pc'[j] = "b1"

============================================================================