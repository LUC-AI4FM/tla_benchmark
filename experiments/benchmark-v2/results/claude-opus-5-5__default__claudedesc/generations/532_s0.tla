---------------------------- MODULE Exponentiation ----------------------------
(***************************************************************************)
(* Computes m^n by repeated multiplication, where m is an integer and n is *)
(* a natural number.                                                       *)
(***************************************************************************)
EXTENDS Integers, Naturals, TLC

CONSTANTS MSet, NSet

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Nat

VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

TypeOK ==
    /\ m \in MSet
    /\ n \in NSet
    /\ res \in Int
    /\ i \in Nat
    /\ pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Done"}

Init ==
    /\ m \in MSet
    /\ n \in NSet
    /\ res = 1
    /\ i = 1
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ Assert(m \in Int /\ n \in Nat,
              "Failure of assertion at line 1: inputs not of expected type")
    /\ pc' = "Lbl_2"
    /\ UNCHANGED << m, n, res, i >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF i <= n
          THEN /\ res' = res * m
               /\ i' = i + 1
               /\ pc' = "Lbl_2"
          ELSE /\ pc' = "Lbl_3"
               /\ UNCHANGED << res, i >>
    /\ UNCHANGED << m, n >>

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ Assert(res = m ^ n,
              "Failure of assertion at line 2: res # m^n")
    /\ pc' = "Done"
    /\ UNCHANGED << m, n, res, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety: once done, the result is m^n.                                   *)
(***************************************************************************)
Correctness == (pc = "Done") => (res = m ^ n)

LoopInvariant == (pc = "Lbl_2") => (res = m ^ (i - 1) /\ i <= n + 1)

(***************************************************************************)
(* Liveness (not enabled in the provided configuration).                   *)
(***************************************************************************)
Termination == <>(pc = "Done")

=============================================================================