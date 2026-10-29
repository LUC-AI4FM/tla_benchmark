---------------------------- MODULE MCSession9alt ----------------------------
(***************************************************************************)
(* Model-checking wrapper for Session9alt.                                 *)
(*                                                                         *)
(* The underlying algorithm (state variable pc, Init, Next, Spec) is      *)
(* inherited from Session9alt. This module adds only:                     *)
(*   - concrete model values for the number of processes and the          *)
(*     process set, to be substituted for the constants of Session9alt    *)
(*     in the model configuration (e.g. N <- MC_N, Procs <- MC_Procs);    *)
(*   - a mutual exclusion safety property;                                *)
(*   - a naive liveness property.                                         *)
(*                                                                         *)
(* The constants, variables, Init, Next, Spec and fairness conditions are *)
(* not redeclared here, because redeclaring them would clash with the     *)
(* definitions inherited through EXTENDS.                                 *)
(***************************************************************************)
EXTENDS Session9alt, Naturals

(***************************************************************************)
(* Concrete model values.                                                  *)
(***************************************************************************)
MC_N == 3

MC_Procs == 1..MC_N

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at the  *)
(* same time.                                                              *)
(***************************************************************************)
MutualExclusion ==
    [](\A p, q \in Procs :
          (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs"))

(***************************************************************************)
(* Naive liveness: every process visits the critical section infinitely   *)
(* often.                                                                  *)
(***************************************************************************)
NaiveLiveness ==
    \A p \in Procs : []<>(pc[p] = "cs")

=============================================================================