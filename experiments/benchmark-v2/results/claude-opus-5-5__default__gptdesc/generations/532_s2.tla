---------------------------- MODULE Exponentiation ----------------------------
(***************************************************************************)
(* Iterative exponentiation: computes m ^ n by repeated multiplication.   *)
(*                                                                         *)
(* --algorithm Exponentiation                                              *)
(*   variables m \in MSet, n \in NSet, res = 1, i = 1;                     *)
(*   begin                                                                 *)
(*     Lbl_1:                                                              *)
(*       while i =< n do                                                   *)
(*         res := res * m;                                                 *)
(*         i := i + 1;                                                     *)
(*       end while;                                                        *)
(*       assert res = m ^ n;                                               *)
(* end algorithm                                                           *)
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
    /\ pc \in {"Lbl_1", "Done"}

Init ==
    /\ m \in MSet
    /\ n \in NSet
    /\ res = 1
    /\ i = 1
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF i =< n
          THEN /\ res' = res * m
               /\ i' = i + 1
               /\ pc' = "Lbl_1"
          ELSE /\ Assert(res = m ^ n,
                         "Failure of assertion: res = m ^ n")
               /\ pc' = "Done"
               /\ UNCHANGED << res, i >>
    /\ UNCHANGED << m, n >>

(* Allow infinite stuttering after termination to prevent deadlock. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* Loop invariant: the accumulator holds m ^ (i - 1). *)
LoopInv == (pc = "Lbl_1") => (i =< n + 1 /\ res = m ^ (i - 1))

(* Partial correctness: on termination, res = m ^ n. *)
Correctness == (pc = "Done") => (res = m ^ n)

(* Eventual termination. *)
Termination == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ LoopInv /\ Correctness)
THEOREM FairSpec => Termination
=============================================================================