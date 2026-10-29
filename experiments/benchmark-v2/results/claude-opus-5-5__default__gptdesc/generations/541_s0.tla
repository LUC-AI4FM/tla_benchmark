---------------------------- MODULE MCSession7 ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the Session7 specification.               *)
(*                                                                         *)
(* All constants, variables (including the PlusCal control-state variable  *)
(* pc and the shared variable x), Init, Next and Spec are imported from    *)
(* Session7. This module adds no variables, actions or temporal formulas.  *)
(* It only defines one state-level correctness condition to check as an    *)
(* invariant.                                                              *)
(***************************************************************************)
EXTENDS Session7

(***************************************************************************)
(* AddCorrect: when both processes "ProcA" and "ProcB" have reached the    *)
(* "Done" control state, the shared variable x equals 2.                   *)
(***************************************************************************)
AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => (x = 2)

=============================================================================