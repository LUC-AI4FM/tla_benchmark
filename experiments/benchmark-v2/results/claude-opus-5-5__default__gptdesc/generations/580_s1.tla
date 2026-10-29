---------------------------- MODULE MCSingleNodeReads ----------------------------
(***************************************************************************)
(* Bounded model-checking wrapper around the single-node read system.     *)
(* CONSTANTS, VARIABLES (including history), Init, vars,                   *)
(* RoTxRequestAction, RoTxResponseAction and MCNextSingleNodeAction are    *)
(* inherited from the extended modules SingleNodeReads and MCSingleNode.   *)
(***************************************************************************)
EXTENDS SingleNodeReads, MCSingleNode

\* Bound on the length of the external history explored by the model checker
MCHistoryBound == 8

\* Read-only transaction request, guarded by the history bound
MCRoTxRequestAction ==
    /\ Len(history) < MCHistoryBound
    /\ RoTxRequestAction

\* Read-only transaction response, guarded by the history bound
MCRoTxResponseAction ==
    /\ Len(history) < MCHistoryBound
    /\ RoTxResponseAction

\* Bounded single-node next-state action extended with read-only transactions
MCNextSingleNodeReadsAction ==
    \/ MCNextSingleNodeAction
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

\* Safety-style specification: start in Init, then evolve by the
\* stuttering closure of MCNextSingleNodeReadsAction over vars
MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReadsAction]_vars

==================================================================================