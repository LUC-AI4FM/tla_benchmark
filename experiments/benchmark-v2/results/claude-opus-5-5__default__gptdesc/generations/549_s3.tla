---------------------------- MODULE MCSession9alt ----------------------------
(***************************************************************************)
(* Model-checking wrapper around Session9alt.                              *)
(* It provides concrete values for the number of processes and the set of *)
(* processes. It also adds a mutual exclusion safety property and a naive  *)
(* liveness property over the inherited variable pc.                       *)
(* The algorithm, which includes Init, Next and Spec, is defined in        *)
(* Session9alt. This module only refers to those definitions.              *)
(***************************************************************************)
EXTENDS Session9alt, Naturals, TLC

(***************************************************************************)
(* Concrete model values for the constants. In the TLC configuration they  *)
(* override the constants of Session9alt, for example:                     *)
(*     CONSTANT N <- const_N                                               *)
(*     CONSTANT Procs <- const_Procs                                       *)
(***************************************************************************)
const_N == 3

const_Procs == 1 .. const_N

(***************************************************************************)
(* Aliases for the inherited initial predicate, next-state relation and    *)
(* specification.                                                          *)
(***************************************************************************)
MCInit == Init

MCNext == Next

MCSpec == Spec

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at the    *)
(* same time.                                                              *)
(***************************************************************************)
MutualExclusion ==
  [](\A i, j \in const_Procs :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs"))

(***************************************************************************)
(* Naive liveness: every process visits the critical section infinitely    *)
(* often.                                                                  *)
(***************************************************************************)
NaiveLiveness ==
  \A p \in const_Procs : []<>(pc[p] = "cs")

=============================================================================