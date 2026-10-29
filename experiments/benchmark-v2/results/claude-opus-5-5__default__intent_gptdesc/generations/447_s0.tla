---------------------------- MODULE RingRegister ----------------------------
(***************************************************************************)
(* A single integer register ranging over the ring 0..N-1 (e.g. 0..4 for   *)
(* N = 5).  Each atomic step reads the register, computes                  *)
(* temp = reg + 1, passes temp through an abstract deterministic modular   *)
(* increment component Inc, and writes Inc(temp) - 1 back to the register. *)
(*                                                                         *)
(* Inc is an abstract constant operator.  Its implementation is not        *)
(* prescribed.  The only requirement is the contract stated in             *)
(* IncContract.  Any deterministic implementation satisfying it can be     *)
(* plugged in, for example by overriding Inc in a TLC model.               *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    N,        \* size of the ring; the register ranges over 0..N-1
    Inc(_)    \* abstract deterministic modular-increment component

ASSUME NAssumption == N \in Nat /\ N >= 1

(***************************************************************************)
(* Contract for the abstract component: on the domain 1..N it behaves as   *)
(* a modular increment within 1..N.  Because Inc is a constant operator,   *)
(* it is fixed throughout every execution.                                 *)
(***************************************************************************)
ASSUME IncContract ==
    \A t \in 1..N : /\ Inc(t) \in 1..N
                    /\ Inc(t) = (t % N) + 1

VARIABLE reg

vars == << reg >>

Ring   == 0..(N - 1)
Target == N - 1

-----------------------------------------------------------------------------
Init == reg = 0

(***************************************************************************)
(* The atomic read-compute-write update.                                   *)
(***************************************************************************)
Update ==
    LET temp == reg + 1
    IN  reg' = Inc(temp) - 1

Next == Update

Spec == Init /\ [][Next]_vars /\ WF_vars(Update)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: the register always stays within the ring.                      *)
(***************************************************************************)
TypeOK == reg \in Ring

Safety == []TypeOK

(***************************************************************************)
(* Liveness: the target value is reached infinitely often.                 *)
(***************************************************************************)
Liveness == []<>(reg = Target)

(***************************************************************************)
(* A weaker form: the target value is reached at least once.               *)
(***************************************************************************)
EventuallyTarget == <>(reg = Target)

THEOREM SafetyTheorem   == Spec => Safety
THEOREM LivenessTheorem == Spec => Liveness
=============================================================================