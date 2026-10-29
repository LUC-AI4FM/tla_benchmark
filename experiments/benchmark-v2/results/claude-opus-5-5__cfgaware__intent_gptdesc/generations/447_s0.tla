---------------------------- MODULE RingRegister ----------------------------
EXTENDS Integers

(***************************************************************************)
(* A single integer register over the ring 0..N-1 (N = 5).                 *)
(* Each step atomically reads the register, computes tmp = reg + 1, passes *)
(* tmp through an abstract deterministic modular increment component, and  *)
(* stores (result - 1) back into the register.                             *)
(***************************************************************************)

N      == 5
Ring   == 0..(N-1)
Target == N - 1

(***************************************************************************)
(* The separate component: a deterministic modular increment function.     *)
(* It is used only through its interface IncComponent(Int) -> Int.         *)
(* Its contract, for inputs t in 1..N:                                     *)
(*    IncComponent(t) - 1 = t % N                                          *)
(* so the register advances by one step around the ring. Any               *)
(* implementation that meets this contract preserves both properties. The  *)
(* definition below is one such implementation.                            *)
(***************************************************************************)
IncComponent(t) == (t % N) + 1

(* The contract that any compliant implementation must satisfy. *)
ComponentContract ==
    \A t \in 1..N : IncComponent(t) - 1 = t % N

VARIABLE reg

vars == << reg >>

Init == reg = 0

(* The atomic read-compute-write update. *)
Update ==
    LET tmp == reg + 1
    IN  reg' = IncComponent(tmp) - 1

Next == Update

Spec == Init /\ [][Next]_vars /\ WF_vars(Update)

(***************************************************************************)
(* Correctness requirements                                                *)
(***************************************************************************)

(* Safety: the register always stays within the ring. *)
TypeOK == reg \in Ring

Safety == []TypeOK

(* Liveness: the target value is reached infinitely often. *)
Liveness == []<>(reg = Target)

THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================