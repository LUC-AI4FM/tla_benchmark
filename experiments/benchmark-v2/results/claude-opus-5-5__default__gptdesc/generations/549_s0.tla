---------------------------- MODULE MCSession9alt ----------------------------
(***************************************************************************)
(* Model-checking wrapper around Session9alt.                              *)
(*                                                                         *)
(* This module defines concrete model values for the constants of the      *)
(* extended specification. It also adds two temporal properties over the   *)
(* inherited state variable pc:                                            *)
(*   - MutualExclusion: no two distinct processes are in the critical      *)
(*     section at the same time.                                           *)
(*   - NaiveLiveness: every process visits the critical section            *)
(*     infinitely often.                                                   *)
(*                                                                         *)
(* The underlying algorithm comes entirely from Session9alt. That includes *)
(* the variables (in particular pc), Init, Next, Spec and any fairness     *)
(* conditions. They are inherited through EXTENDS and are not redefined    *)
(* here.                                                                   *)
(***************************************************************************)
EXTENDS Session9alt, Naturals, FiniteSets, TLC

---------------------------------------------------------------------------
(***************************************************************************)
(* Concrete model values, substituted for the constants of Session9alt in  *)
(* the TLC model configuration:                                            *)
(*     CONSTANT N <- MC_N                                                  *)
(*     CONSTANT Procs <- MC_Procs                                          *)
(***************************************************************************)
MC_N == 3

MC_Procs == 1 .. MC_N

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety: no two distinct processes are simultaneously in the critical    *)
(* section.                                                                *)
(***************************************************************************)
InCS(p) == pc[p] = "cs"

MutualExclusion ==
    [](\A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j)))

(***************************************************************************)
(* Naive liveness: every process visits the critical section infinitely   *)
(* often.                                                                  *)
(***************************************************************************)
NaiveLiveness ==
    \A p \in Procs : []<>(InCS(p))

---------------------------------------------------------------------------
(***************************************************************************)
(* Specification checked by the model: the inherited Spec of Session9alt.  *)
(***************************************************************************)
MCSpec == Spec

THEOREM MCSpec => MutualExclusion
THEOREM MCSpec => NaiveLiveness
=============================================================================