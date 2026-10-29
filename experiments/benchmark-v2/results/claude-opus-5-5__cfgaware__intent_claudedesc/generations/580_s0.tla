---- MODULE MCSingleNodeReads ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived

CONSTANTS CommittedStatus, InvalidStatus

CONSTANT HistoryLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* Base definitions
FirstBranch == 1

Views == Nat
SeqNums == Nat
TxIDs == Views \X SeqNums
TxStatuses == {CommittedStatus, InvalidStatus}
Txs == Nat

Range(s) == {s[i] : i \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Ledger == ledgerBranches[FirstBranch]

LedgerTxs == [k \in 1..Len(Ledger) |-> Ledger[k].tx]

ResponseTypes == {RwTxResponse, RoTxResponse}
RequestTypes == {RwTxRequest, RoTxRequest}

CommittedTxIDs ==
    {history[k].tx_id : k \in {m \in DOMAIN history :
        /\ history[m].type = TxStatusReceived
        /\ history[m].status = CommittedStatus}}

InvalidTxIDs ==
    {history[k].tx_id : k \in {m \in DOMAIN history :
        /\ history[m].type = TxStatusReceived
        /\ history[m].status = InvalidStatus}}

\* Initial state
Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

\* Base single node actions

\* A client sends a new read-write transaction request
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* The node executes a requested read-write transaction, appending it to the ledger
RwTxExecuteAction ==
    \E i \in DOMAIN history:
        /\ history[i].type = RwTxRequest
        /\ \A k \in DOMAIN Ledger: Ledger[k].tx # history[i].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![FirstBranch] =
                Append(@, [view |-> FirstBranch, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* The node responds to an executed read-write transaction
RwTxResponseAction ==
    \E i \in DOMAIN Ledger:
        /\ \A j \in DOMAIN history:
            ~(/\ history[j].type = RwTxResponse
              /\ history[j].tx = Ledger[i].tx)
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> Ledger[i].tx,
                 observed |-> SubSeq(LedgerTxs, 1, i),
                 tx_id |-> <<Ledger[i].view, i>>])
        /\ UNCHANGED ledgerBranches

\* The client learns that a transaction has committed (single node: immediate commit)
StatusCommittedResponseAction ==
    \E i \in DOMAIN history:
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id[2] <= Len(Ledger)
        /\ \A j \in DOMAIN history:
            ~(/\ history[j].type = TxStatusReceived
              /\ history[j].tx_id = history[i].tx_id)
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* Read-only transaction actions

\* A client sends a new read-only transaction request
RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* The node responds to a read-only transaction with a snapshot of the ledger
RoTxResponseAction ==
    \E i \in DOMAIN history:
        /\ history[i].type = RoTxRequest
        /\ \A j \in DOMAIN history:
            ~(/\ history[j].type = RoTxResponse
              /\ history[j].tx = history[i].tx)
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> LedgerTxs,
                 tx_id |-> <<FirstBranch, Len(Ledger)>>])
        /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

\* Model checking bounds
MCNextSingleNodeReads ==
    /\ Len(history) < HistoryLimit
    /\ NextSingleNodeReadsAction

MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReads]_vars

\* Invariants

\* Every response was preceded by a matching request
AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history:
        history[i].type \in ResponseTypes =>
            \E j \in 1..(i - 1):
                /\ history[j].type =
                    (IF history[i].type = RwTxResponse THEN RwTxRequest ELSE RoTxRequest)
                /\ history[j].tx = history[i].tx

\* Once a transaction is known committed, all later read-write responses observe it
AllCommittedObservedInv ==
    \A i, j \in DOMAIN history:
        (/\ i < j
         /\ history[i].type = TxStatusReceived
         /\ history[i].status = CommittedStatus
         /\ history[j].type = RwTxResponse)
        => \A k \in DOMAIN history:
            (/\ history[k].type = RwTxResponse
             /\ history[k].tx_id = history[i].tx_id)
            => history[k].tx \in Range(history[j].observed)

\* Once a transaction is known committed, all later read-only responses observe it
AllCommittedObservedRoInv ==
    \A i, j \in DOMAIN history:
        (/\ i < j
         /\ history[i].type = TxStatusReceived
         /\ history[i].status = CommittedStatus
         /\ history[j].type = RoTxResponse)
        => \A k \in DOMAIN history:
            (/\ history[k].type = RwTxResponse
             /\ history[k].tx_id = history[i].tx_id)
            => history[k].tx \in Range(history[j].observed)

\* Responses only observe read-write transactions that were previously requested
OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history:
        history[i].type \in ResponseTypes =>
            \A t \in Range(history[i].observed):
                \E j \in 1..(i - 1):
                    /\ history[j].type = RwTxRequest
                    /\ history[j].tx = t

\* Each transaction is requested at most once and responded to at most once
UniqueTxsInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type \in RequestTypes \cup ResponseTypes
         /\ history[j].type = history[i].type
         /\ history[i].tx = history[j].tx)
        => i = j

\* Read-write responses have unique transaction ids
UniqueTxIdsInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id = history[j].tx_id)
        => i = j

\* Read-write responses have unique sequence numbers
UniqueSeqNumsInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id[2] = history[j].tx_id[2])
        => i = j

\* A transaction is never both committed and invalid
CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx_id = history[j].tx_id)
        => history[i].status = history[j].status

\* Read-write transactions are serializable: observations are totally ordered by prefix
RwSerializableInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse)
        => \/ IsPrefix(history[i].observed, history[j].observed)
           \/ IsPrefix(history[j].observed, history[i].observed)

\* Committed read-write transactions are serializable
CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history:
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id \in CommittedTxIDs
         /\ history[j].tx_id \in CommittedTxIDs)
        => \/ IsPrefix(history[i].observed, history[j].observed)
           \/ IsPrefix(history[j].observed, history[i].observed)

\* Invalid transactions are not observed by any other transaction
InvalidNotObservedInv ==
    \A i, j \in DOMAIN history:
        (/\ i # j
         /\ history[i].type = RwTxResponse
         /\ history[j].type \in ResponseTypes
         /\ history[i].tx_id \in InvalidTxIDs)
        => history[i].tx \notin Range(history[j].observed)

\* Invalid transactions are not observed by any committed transaction
InvalidNotObservedByCommittedInv ==
    \A i, j \in DOMAIN history:
        (/\ i # j
         /\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id \in InvalidTxIDs
         /\ history[j].tx_id \in CommittedTxIDs)
        => history[i].tx \notin Range(history[j].observed)

\* Each transaction is observed at most once within any observation
AtMostOnceObservedInv ==
    \A i \in DOMAIN history:
        history[i].type \in ResponseTypes =>
            \A a, b \in DOMAIN history[i].observed:
                a # b => history[i].observed[a] # history[i].observed[b]

====