---- MODULE MCSingleNodeReads ----
(***************************************************************************)
(* Bounded model-checking wrapper around the single-node read system.      *)
(*                                                                         *)
(* SingleNodeReads defines the single-node system together with the       *)
(* read-only transaction actions RoTxRequestAction and RoTxResponseAction. *)
(* MCSingleNode defines the bounded single-node next-state action          *)
(* MCNextSingleNodeAction and the bound constant HistMaxLen.               *)
(*                                                                         *)
(* The constants (including HistMaxLen), the variables (including          *)
(* history), vars and Init all come from these extended modules, so they   *)
(* are not declared again here.                                            *)
(***************************************************************************)
EXTENDS SingleNodeReads, MCSingleNode

(***************************************************************************)
(* History-bound guards on the read-only transaction actions.              *)
(***************************************************************************)
MCRoTxRequestAction ==
    /\ Len(history) < HistMaxLen
    /\ RoTxRequestAction

MCRoTxResponseAction ==
    /\ Len(history) < HistMaxLen
    /\ RoTxResponseAction

(***************************************************************************)
(* Combined bounded next-state action.                                     *)
(***************************************************************************)
MCNextSingleNodeReadsAction ==
    \/ MCNextSingleNodeAction
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

MCNext == MCNextSingleNodeReadsAction

(***************************************************************************)
(* Safety-style specification: start in Init, then take steps of          *)
(* MCNextSingleNodeReadsAction or stutter on vars.                         *)
(***************************************************************************)
MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReadsAction]_vars

MCSpec == MCSpecSingleNodeReads

====