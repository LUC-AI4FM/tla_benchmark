---------------------------- MODULE MCSession9alt ----------------------------
(***************************************************************************)
(* Model-checking wrapper around Session9alt.                              *)
(*                                                                         *)
(* The underlying algorithm, including its CONSTANTS, VARIABLES (in       *)
(* particular pc), Init, Next and Spec, is inherited from Session9alt via  *)
(* EXTENDS. This module adds only:                                          *)
(*   - concrete model values for the number of processes and the process   *)
(*     set, which are substituted for the constants in the TLC model       *)
(*     (N <- MCN, Procs <- MCProcs), and                                    *)
(*   - two temporal properties over the inherited variable pc.             *)
(***************************************************************************)
EXTENDS Session9alt, Naturals, FiniteSets

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete model values                                                    *)
(***************************************************************************)

\* Number of processes used for model checking
MCN == 3

\* The set of process identifiers used for model checking
MCProcs == 1..MCN

-----------------------------------------------------------------------------
(***************************************************************************)
(* The behaviour specification is inherited from Session9alt.              *)
(* MCInit, MCNext and MCSpec are aliases for the inherited definitions,     *)
(* so the TLC model can refer to them directly.                            *)
(***************************************************************************)

MCInit == Init

MCNext == Next

MCSpec == Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: mutual exclusion.                                                *)
(* No two distinct processes are in the critical section at the same time. *)
(***************************************************************************)
MutualExclusion ==
    [] (\A i, j \in Procs :
            (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs"))

(***************************************************************************)
(* Liveness (naive): every process visits the critical section infinitely  *)
(* often.                                                                   *)
(***************************************************************************)
NaiveLiveness ==
    \A p \in Procs : []<>(pc[p] = "cs")

=============================================================================