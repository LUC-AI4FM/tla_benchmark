-------------------------- MODULE MCSession9alt --------------------------
(***************************************************************************)
(* Model-checking wrapper around Session9alt.                              *)
(*                                                                         *)
(* The underlying algorithm (variables, Init, Next, Spec and any fairness  *)
(* conditions) is defined in Session9alt and inherited through EXTENDS.    *)
(* Init, Next and Spec are not redefined here, because redefining them     *)
(* would clash with the inherited definitions. This module only adds:      *)
(*   - concrete model values for the number of processes and the process   *)
(*     set, which the TLC configuration substitutes for the constants      *)
(*     N and Procs (for example, N <- MCN and Procs <- MCProcs);           *)
(*   - a mutual exclusion safety property over pc;                         *)
(*   - a naive liveness property over pc.                                  *)
(***************************************************************************)
EXTENDS Session9alt, Naturals, TLC

(***************************************************************************)
(* Concrete model values                                                   *)
(***************************************************************************)
MCN == 3

MCProcs == 1..MCN

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at the    *)
(* same time.                                                              *)
(***************************************************************************)
MutualExclusion ==
    [](\A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs"))

(***************************************************************************)
(* Liveness (naive): every process is in the critical section infinitely   *)
(* often.                                                                  *)
(***************************************************************************)
NaiveLiveness ==
    \A p \in Procs : []<>(pc[p] = "cs")

=============================================================================