---------------------------- MODULE MCSingleNode ----------------------------
(***************************************************************************)
(* Bounded version of the single-node transaction processing system,       *)
(* intended for model checking. The base module SingleNode is assumed to   *)
(* define: vars, history, Init, RwTxRequestAction, RwTxExecuteAction,      *)
(* RwTxResponseAction, StatusCommittedResponseAction, and the invariants   *)
(* checked by the configuration.                                           *)
(***************************************************************************)
EXTENDS SingleNode, Naturals, Sequences

\* Upper bound on the length of the transaction history (7 in the config)
CONSTANT HistoryLimit

ASSUME HistoryLimit \in Nat

\* Bounded request of a read-write transaction
MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

\* Bounded response to a read-write transaction
MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

\* Bounded response to a status-committed query
MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

\* Bounded next-state relation. Execution is not bounded by the history
\* length, since it does not extend the history.
MCNextSingleNode ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCStatusCommittedResponseAction

MCInit == Init

MCNext == MCNextSingleNode

\* Temporal specification: initial state from the base module, with
\* stuttering-allowed steps of the bounded next-state relation.
MCSpecSingleNode == Init /\ [][MCNextSingleNode]_vars

Spec == MCSpecSingleNode

(***************************************************************************)
(* Configuration (MCSingleNode.cfg):                                       *)
(*                                                                         *)
(*   SPECIFICATION MCSpecSingleNode                                        *)
(*   CONSTANTS HistoryLimit = 7                                            *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(*   INVARIANTS                                                            *)
(*     AllRwReceivedIsFirstSentInv                                         *)
(*     AllReceivedIsFirstSentInv                                           *)
(*     UniqueTxsInv                                                        *)
(*     UniqueTxIdsInv                                                      *)
(*     UniqueSeqNumsInv                                                    *)
(*     UniqueTxRequestsInv                                                 *)
(*     CommittedRwSerializableInv                                          *)
(*     AllCommittedObservedInv                                             *)
(*     OnlyObserveSentRequestsInv                                          *)
(*     SerializableRwTxsInv                                                *)
(*     InvalidNotObservedByCommittedInv                                    *)
(*     CommittedOrInvalidStrongInv                                         *)
(*                                                                         *)
(* Deadlock checking is disabled because reaching HistoryLimit may         *)
(* legitimately leave no enabled bounded actions.                          *)
(***************************************************************************)
=============================================================================