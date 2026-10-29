---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* Model-checking companion module for Session3proj.                       *)
(*                                                                         *)
(* It extends the underlying specification and supplies two constant,      *)
(* set-valued definitions. These are concrete integer domains or           *)
(* parameter sets used to instantiate the constants of Session3proj when   *)
(* running TLC.                                                            *)
(*                                                                         *)
(* This module declares no variables, actions, temporal formulas,          *)
(* fairness conditions, proofs, or PlusCal algorithm of its own. Init,     *)
(* Next, Spec and all invariants and properties are inherited unchanged    *)
(* from Session3proj. Redefining them here would be a duplicate-definition *)
(* error.                                                                  *)
(***************************************************************************)
EXTENDS Session3proj, TLC

\* First fixed integer set, used as a concrete domain / parameter set.
const_1 == {1, 2, 3}

\* Second fixed integer set, used as a concrete domain / parameter set.
const_2 == {0, 1, 2, 3, 4}

=============================================================================