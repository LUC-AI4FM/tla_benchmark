------------------------------ MODULE SimpleUpdate ------------------------------
VARIABLES S, A

(* ------------------------------------------------------------------------- *)
(*  Initial state: the set contains two distinct symbols and the sequence   *)
(*  has three integer entries with specified initial values.                 *)
(* ------------------------------------------------------------------------- *)

Init == 
  /\ S = {"a", "b"}
  /\ A = <<1, 2, 3>>

(* ------------------------------------------------------------------------- *)
(*  Update step: add one new symbol to the set and overwrite the second     *)
(*  element of the sequence with a new integer. No other components may    *)
(*  change during this step.                                               *)
(* ------------------------------------------------------------------------- *)

UpdateStep ==
  /\ S = {"a", "b"}                     \* pre‑condition: still initial
  /\ A = <<1, 2, 3>>                    \* pre‑condition: still initial
  /\ S' = S ∪ { "c" }                   \* add new symbol
  /\ A' = <<A[1], 42, A[3]>>             \* overwrite second element

(* ------------------------------------------------------------------------- *)
(*  Stuttering step: no change. Allows the system to remain in the final   *)
(*  state forever without further changes.                                 *)
(* ------------------------------------------------------------------------- *)

Stutter ==
  /\ S' = S
  /\ A' = A

Next == UpdateStep \/ Stutter

(* ------------------------------------------------------------------------- *)
(*  The main specification: initial condition, temporal evolution, and     *)
(*  liveness requirement that the update eventually occurs.               *)
(* ------------------------------------------------------------------------- *)

Spec == Init 
        /\ [][Next]_<<S, A>> 
        /\ <> (S = {"a", "b"} ∪ { "c" } /\ A = <<1, 42, 3>>)

=============================================================================