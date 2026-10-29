---------------------------- MODULE MCMultiNode ----------------------------
(***************************************************************************)
(* Bounded model-checking wrapper for the MultiNode specification.         *)
(* The base MultiNode definitions are given inline so that the module is   *)
(* self-contained. The wrapper adds the constant ViewLimit to bound the    *)
(* number of view changes. It guards the inherited actions with checks on  *)
(* Len(ledgerBranches) and Len(history), and defines MCSpecMultiNode.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

-----------------------------------------------------------------------------
(*************************** Base MultiNode part ***************************)

CONSTANT HistoryLimit      \* bound on the number of client-observed events

VARIABLES history,         \* sequence of client-observed events
          ledgerBranches   \* ledgerBranches[v] is the ledger branch in view v

vars == <<history, ledgerBranches>>

CurrentView   == Len(ledgerBranches)
CurrentLedger == ledgerBranches[CurrentView]

RwTxRequestType  == "RwTxRequest"
RwTxResponseType == "RwTxResponse"
TxStatusType     == "TxStatusReceived"
CommittedStatus  == "Committed"
InvalidStatus    == "Invalid"

\* Ledger entries are either client transactions or other (internal) txns
LedgerEntry(v, kind, t) == [view |-> v, kind |-> kind, tx |-> t]

RequestedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history :
                                history[j].type = RwTxRequestType } }

RespondedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history :
                                history[j].type = RwTxResponseType } }

InLedger(t, ledger) ==
    \E i \in DOMAIN ledger : ledger[i].kind = "client" /\ ledger[i].tx = t

StatusReported(t) ==
    \E i \in DOMAIN history :
        history[i].type = TxStatusType /\ history[i].tx = t

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ history' = Append(history,
                    [type |-> RwTxRequestType, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* The primary of the current view executes a requested transaction
RwTxExecuteAction ==
    /\ \E t \in RequestedTxs :
        /\ ~InLedger(t, CurrentLedger)
        /\ t \notin RespondedTxs
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                                Append(@, LedgerEntry(CurrentView, "client", t))]
    /\ UNCHANGED history

\* The client receives a response with the transaction ID <<view, seqno>>
RwTxResponseAction ==
    /\ \E i \in DOMAIN CurrentLedger :
        /\ CurrentLedger[i].kind = "client"
        /\ CurrentLedger[i].tx \notin RespondedTxs
        /\ history' = Append(history,
                        [type  |-> RwTxResponseType,
                         tx    |-> CurrentLedger[i].tx,
                         tx_id |-> <<CurrentLedger[i].view, i>>])
    /\ UNCHANGED ledgerBranches

\* The client learns that a transaction was committed
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponseType
        /\ ~StatusReported(history[i].tx)
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN  /\ s \in DOMAIN CurrentLedger
               /\ CurrentLedger[s].view = v
               /\ history' = Append(history,
                               [type   |-> TxStatusType,
                                tx     |-> history[i].tx,
                                status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* The client learns that a transaction was invalidated by a view change
StatusInvalidResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponseType
        /\ ~StatusReported(history[i].tx)
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN  /\ CurrentView > v
               /\ \/ s \notin DOMAIN CurrentLedger
                  \/ CurrentLedger[s].view # v
               /\ history' = Append(history,
                               [type   |-> TxStatusType,
                                tx     |-> history[i].tx,
                                status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* The primary appends an internal (non-client) transaction
AppendOtherTxnAction ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                            Append(@, LedgerEntry(CurrentView, "other", 0))]
    /\ UNCHANGED history

\* A view change: the new view's branch is a prefix of the current ledger
TruncateLedgerAction ==
    /\ \E i \in 0..Len(CurrentLedger) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentLedger, 1, i))
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ AppendOtherTxnAction
    \/ TruncateLedgerAction

Spec == Init /\ [][Next]_vars

\* Safety invariants
TypeOK ==
    /\ history \in Seq([type : {RwTxRequestType}, tx : Nat]
                       \cup [type : {RwTxResponseType}, tx : Nat,
                             tx_id : Nat \X Nat]
                       \cup [type : {TxStatusType}, tx : Nat,
                             status : {CommittedStatus, InvalidStatus}])
    /\ Len(ledgerBranches) >= 1

OneResponsePerTx ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RwTxResponseType
        /\ history[j].type = RwTxResponseType
        /\ history[i].tx = history[j].tx
        => i = j

OneStatusPerTx ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = TxStatusType
        /\ history[j].type = TxStatusType
        /\ history[i].tx = history[j].tx
        => i = j

ResponsesFollowRequests ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponseType => history[i].tx \in RequestedTxs

-----------------------------------------------------------------------------
(*************************** Bounded MC wrapper ****************************)

CONSTANT ViewLimit

ASSUME ViewLimit \in Nat \ {0}
ASSUME HistoryLimit \in Nat

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRwTxExecuteAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxExecuteAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCStatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusInvalidResponseAction

MCAppendOtherTxnAction ==
    /\ Len(ledgerBranches[Len(ledgerBranches)]) < HistoryLimit
    /\ AppendOtherTxnAction

MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

MCNextMultiNodeAction ==
    \/ MCRwTxRequestAction
    \/ MCRwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCStatusCommittedResponseAction
    \/ MCStatusInvalidResponseAction
    \/ MCAppendOtherTxnAction
    \/ MCTruncateLedgerAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

\* Bound on view changes holds in every reachable state
ViewBoundInv == Len(ledgerBranches) <= ViewLimit

=============================================================================