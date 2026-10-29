---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT HistoryLimit

ASSUME HistoryLimit \in Nat

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* Single node, so there are no view changes: only one view exists
Views == {1}
CurrentView == 1

SeqNums == Nat \ {0}

TxIDs == Views \X SeqNums

\* Abstract transaction identifiers carried in requests
Txs == Nat

\* Event types in the external history
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
TxStatuses == {CommittedStatus}

RwTxRequests == [type : {RwTxRequest}, tx : Txs]

RwTxResponses == [type : {RwTxResponse}, tx : Txs, tx_id : TxIDs]

TxStatusReceiveds == [type : {TxStatusReceived}, tx_id : TxIDs, status : TxStatuses]

HistoryEvents == RwTxRequests \cup RwTxResponses \cup TxStatusReceiveds

\* Ledger entries: either a client read-write transaction or an unrelated transaction
TxLedgerEntries    == [view : Views, tx : Txs]
OtherLedgerEntries == [view : Views]
LedgerEntries == TxLedgerEntries \cup OtherLedgerEntries

HistoryTypeOK ==
    \A i \in DOMAIN history : history[i] \in HistoryEvents

LedgerTypeOK ==
    /\ DOMAIN ledgerBranches = Views
    /\ \A v \in Views :
         \A i \in DOMAIN ledgerBranches[v] : ledgerBranches[v][i] \in LedgerEntries

TypeOK ==
    /\ history \in Seq(HistoryEvents)
    /\ HistoryTypeOK
    /\ LedgerTypeOK

\* Sequence prefix helper
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

\* Ledger branches only ever grow by appending (temporal property)
AppendOnlyProp ==
    [][\A v \in Views : IsPrefix(ledgerBranches[v], ledgerBranches'[v])]_vars

HasTx(e) == "tx" \in DOMAIN e

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in Views |-> <<>>]

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* The node executes a submitted request, appending it to its ledger
RwTxExecuteAction ==
    /\ Len(ledgerBranches[CurrentView]) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN ledgerBranches[CurrentView] :
             ~(HasTx(ledgerBranches[CurrentView][j])
               /\ ledgerBranches[CurrentView][j].tx = history[i].tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                                Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* The node responds to an executed transaction with its transaction ID
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN ledgerBranches[CurrentView] :
        LET e == ledgerBranches[CurrentView][i] IN
        /\ HasTx(e)
        /\ \E j \in DOMAIN history :
             history[j].type = RwTxRequest /\ history[j].tx = e.tx
        /\ \A j \in DOMAIN history :
             ~(history[j].type = RwTxResponse /\ history[j].tx = e.tx)
        /\ history' = Append(history,
                [type |-> RwTxResponse, tx |-> e.tx, tx_id |-> <<CurrentView, i>>])
        /\ UNCHANGED ledgerBranches

\* With a single node, every ledger entry is committed; report committed status
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET tid == history[i].tx_id IN
           /\ tid[2] <= Len(ledgerBranches[tid[1]])
           /\ \A j \in DOMAIN history :
                ~(history[j].type = TxStatusReceived
                  /\ history[j].tx_id = tid
                  /\ history[j].status = CommittedStatus)
           /\ history' = Append(history,
                  [type |-> TxStatusReceived, tx_id |-> tid, status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* The node appends a transaction unrelated to client requests
AppendOtherTxnAction ==
    /\ Len(ledgerBranches[CurrentView]) < HistoryLimit
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                            Append(@, [view |-> CurrentView])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => AppendOnlyProp

=============================================================================