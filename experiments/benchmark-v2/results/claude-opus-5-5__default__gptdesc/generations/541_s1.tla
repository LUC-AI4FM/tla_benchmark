---------------------------- MODULE MCSession7 ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the Session7 specification.               *)
(* CONSTANTS, VARIABLES, Init, Next and Spec all come from Session7.       *)
(* Redefining them here would clash with the imported names.               *)
(***************************************************************************)
EXTENDS Session7

(***************************************************************************)
(* Safety invariant: once both processes reach the "Done" control state,   *)
(* the shared variable x must equal 2.                                     *)
(***************************************************************************)
AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => (x = 2)

=============================================================================