---------------------------- MODULE SingleNodeTxSystem ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS HistoryLimit

ASSUME HistoryLimit \in Nat /\ HistoryLimit > 0

VARIABLES
    history,   \* Sequence of observable events (requests, responses, status responses)
    ledger     \* Sequence of executed (committed) transaction ids, in execution order

vars == << history, ledger >>

-----------------------------------------------------------------------------
\* Constants and helper definitions

RwTxRequestType       == "RwTxRequest"
RwTxResponseType      == "RwTxResponse"
TxStatusReceivedType  == "TxStatusReceived"

CommittedStatus == "Committed"

\* A transaction id is derived from the history length at request time,
\* so it can never exceed the history bound.
TxIDs == 1..HistoryLimit

SeqNums == 1..HistoryLimit

Events ==
    [type : {RwTxRequestType}, tx : TxIDs]
    \cup [type : {RwTxResponseType}, tx : TxIDs, seqno : SeqNums]
    \cup [type : {TxStatusReceivedType}, tx : TxIDs, status : {CommittedStatus}]

HistoryIndices == 1..Len(history)

RequestedTxs ==
    { history[i].tx : i \in { j \in HistoryIndices : history[j].type = RwTxRequestType } }

RespondedTxs ==
    { history[i].tx : i \in { j \in HistoryIndices : history[j].type = RwTxResponseType } }

StatusReceivedTxs ==
    { history[i].tx : i \in { j \in HistoryIndices : history[j].type = TxStatusReceivedType } }

LedgerTxs == { ledger[i] : i \in 1..Len(ledger) }

IndexOf(t) == CHOOSE i \in 1..Len(ledger) : ledger[i] = t

\* Bound applied uniformly to every action that extends the observable history
HistoryBound == Len(history) < HistoryLimit

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = << >>
    /\ ledger = << >>

-----------------------------------------------------------------------------
\* Actions

\* A client submits a new read-write transaction request
RwTxRequest ==
    /\ HistoryBound
    /\ LET t == Len(history) + 1
       IN history' = Append(history, [type |-> RwTxRequestType, tx |-> t])
    /\ UNCHANGED ledger

\* The node executes a previously requested transaction (internal step, not bounded)
RwTxExecute ==
    /\ \E t \in RequestedTxs :
         /\ t \notin LedgerTxs
         /\ ledger' = Append(ledger, t)
    /\ UNCHANGED history

\* The node responds to the client after the transaction is executed
RwTxResponse ==
    /\ HistoryBound
    /\ \E t \in LedgerTxs :
         /\ t \notin RespondedTxs
         /\ history' = Append(history,
                [type |-> RwTxResponseType, tx |-> t, seqno |-> IndexOf(t)])
    /\ UNCHANGED ledger

\* A client queries the commit status of a responded transaction and
\* the node answers that it has been committed
StatusCommittedResponse ==
    /\ HistoryBound
    /\ \E t \in RespondedTxs :
         /\ t \in LedgerTxs
         /\ t \notin StatusReceivedTxs
         /\ history' = Append(history,
                [type |-> TxStatusReceivedType, tx |-> t, status |-> CommittedStatus])
    /\ UNCHANGED ledger

Next ==
    \/ RwTxRequest
    \/ RwTxExecute
    \/ RwTxResponse
    \/ StatusCommittedResponse

Spec == Init /\ [][Next]_vars /\ WF_vars(RwTxExecute)

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ history \in Seq(Events)
    /\ Len(history) <= HistoryLimit
    /\ ledger \in Seq(TxIDs)

\* Every transaction in the ledger was requested
LedgerOnlyRequested == LedgerTxs \subseteq RequestedTxs

\* No transaction is executed twice
LedgerNoDuplicates ==
    \A i, j \in 1..Len(ledger) : ledger[i] = ledger[j] => i = j

\* Responses only for executed transactions, preceded by their request,
\* and with a sequence number matching the ledger position
ResponsesValid ==
    \A i \in HistoryIndices :
        history[i].type = RwTxResponseType =>
            /\ history[i].tx \in LedgerTxs
            /\ ledger[history[i].seqno] = history[i].tx
            /\ \E j \in 1..(i-1) :
                 /\ history[j].type = RwTxRequestType
                 /\ history[j].tx = history[i].tx

\* At most one response per transaction
UniqueResponses ==
    \A i, j \in HistoryIndices :
        /\ history[i].type = RwTxResponseType
        /\ history[j].type = RwTxResponseType
        /\ history[i].tx = history[j].tx
        => i = j

\* Committed status is only reported for transactions that were committed
\* and whose response was already sent
CommittedStatusValid ==
    \A i \in HistoryIndices :
        history[i].type = TxStatusReceivedType =>
            /\ history[i].tx \in LedgerTxs
            /\ \E j \in 1..(i-1) :
                 /\ history[j].type = RwTxResponseType
                 /\ history[j].tx = history[i].tx

\* Request ids are unique
UniqueRequests ==
    \A i, j \in HistoryIndices :
        /\ history[i].type = RwTxRequestType
        /\ history[j].type = RwTxRequestType
        /\ history[i].tx = history[j].tx
        => i = j

Inv ==
    /\ TypeOK
    /\ LedgerOnlyRequested
    /\ LedgerNoDuplicates
    /\ ResponsesValid
    /\ UniqueResponses
    /\ CommittedStatusValid
    /\ UniqueRequests

-----------------------------------------------------------------------------
\* Liveness properties

\* Every requested transaction is eventually executed (committed)
EventuallyExecuted ==
    \A t \in TxIDs : (t \in RequestedTxs) ~> (t \in LedgerTxs)

\* Once committed, a transaction remains committed
CommittedStable ==
    \A t \in TxIDs : [](t \in LedgerTxs => [](t \in LedgerTxs))

=============================================================================