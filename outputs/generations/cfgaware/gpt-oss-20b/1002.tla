------------------------------ MODULE Barrier ------------------------------
EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLE pc

(* Initial state: all processes start at b0 *)
Init == 
  /\ pc \in [1..N -> {"b0","b1"}]
  /\ ∀ i ∈ 1..N : pc[i] = "b0"

(* Type correctness condition for the program counter function *)
TypeOK ==
  /\ pc \in [1..N -> {"b0","b1"}]
  /\ ∀ i ∈ 1..N : pc[i] ∈ {"b0","b1"}

(* Next-state relation: a single process may move from b0 to b1,
   or if all are in b1, they reset simultaneously to b0 *)
Next ==
  \/ (∃ i ∈ 1..N : pc[i] = "b0" /\ pc' = [pc EXCEPT ![i] = "b1"])
  \/ (∀ i ∈ 1..N : pc[i] = "b1" /\ pc' = [pc EXCEPT ![*] = "b0"])

(* The complete specification *)
Spec == Init /\ [][Next]_pc

(* Temporal barrier property: a process cannot leave the barrier
   while some other process has not yet entered it. *)
BarrierProperty ==
  [] (∀ i ∈ 1..N :
        pc[i] = "b1"
      => ¬(∃ j ∈ 1..N : pc[j] = "b0" /\ pc'[i] = "b0"))

=============================================================================