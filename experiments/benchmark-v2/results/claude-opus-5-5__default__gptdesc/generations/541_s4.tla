---- MODULE Session7MC ----
EXTENDS Session7

(***************************************************************************)
(* Model-checking wrapper around the Session7 specification.               *)
(* Init, Next, Spec, the variables (x, pc) and the processes "ProcA" and   *)
(* "ProcB" all come from Session7. This module adds only one state-level  *)
(* correctness property, to be checked as an invariant.                    *)
(***************************************************************************)

AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => (x = 2)

====