---------------------------- MODULE MCSingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    HistoryLimit,
    FirstBranch,
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus

VARIABLES
    history,         \* sequence of externally observable events
    ledgerBranches,  \* function: branch -> sequence of executed rw txs
    commitSeqNum     \* highest durably applied sequence number

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
\* Helpers

Range(s) == { s[i] : i \in DOMAIN s }

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

Ledger == ledgerBranches[FirstBranch]

HIdx == DOMAIN history

IsRwReq(i)  == history[i].type = RwTxRequest
IsRwResp(i) == history[i].type = RwTxResponse
IsRoReq(i)  == history[i].type = RoTxRequest
IsRoResp(i) == history[i].type = RoTxResponse
IsResp(i)   == IsRwResp(i) \/ IsRoResp(i)
IsStatus(i) == history[i].type = TxStatusReceived

IsCommitted(i) == IsStatus(i) /\ history[i].status = CommittedStatus
IsInvalid(i)   == IsStatus(i) /\ history[i].status = InvalidStatus

RespondedTxs == { history[i].tx : i \in { j \in HIdx : IsResp(j) } }

CommittedTxIds == { history[i].tx_id : i \in { j \in HIdx : IsCommitted(j) } }
InvalidTxIds   == { history[i].tx_id : i \in { j \in HIdx : IsInvalid(j) } }

\* txs (request ids) whose rw response carries a tx_id in the given set
TxsOfTxIds(S) ==
    { history[i].tx : i \in { j \in HIdx : IsRwResp(j) /\ history[j].tx_id \in S } }

CommittedRwRespIdx ==
    { i \in HIdx : IsRwResp(i) /\ history[i].tx_id \in CommittedTxIds }

HistoryNotFull == Len(history) < HistoryLimit

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = << >>
    /\ ledgerBranches = [b \in {FirstBranch} |-> << >>]
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
\* Actions

\* A client issues a new read-write transaction request
RwTxRequestAction ==
    /\ HistoryNotFull
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The node atomically executes a pending rw request against the sequential store
RwTxExecuteAction ==
    /\ \E i \in HIdx :
        /\ IsRwReq(i)
        /\ history[i].tx \notin Range(Ledger)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![FirstBranch] = Append(@, history[i].tx)]
    /\ UNCHANGED <<history, commitSeqNum>>

\* The node responds to an executed rw request, reporting the state it observed
RwTxResponseAction ==
    /\ HistoryNotFull
    /\ \E s \in DOMAIN Ledger :
        /\ Ledger[s] \notin RespondedTxs
        /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> Ledger[s],
                 observed |-> SubSeq(Ledger, 1, s),
                 tx_id    |-> <<FirstBranch, s>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* A client issues a new read-only transaction request
RoTxRequestAction ==
    /\ HistoryNotFull
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The node executes and responds to a read-only request using the current state
RoTxResponseAction ==
    /\ HistoryNotFull
    /\ \E i \in HIdx :
        /\ IsRoReq(i)
        /\ history[i].tx \notin RespondedTxs
        /\ history' = Append(history,
                [type     |-> RoTxResponse,
                 tx       |-> history[i].tx,
                 observed |-> Ledger,
                 tx_id    |-> <<FirstBranch, Len(Ledger)>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Executed transactions become durably applied (committed)
CommitAction ==
    /\ commitSeqNum < Len(Ledger)
    /\ \E s \in (commitSeqNum + 1)..Len(Ledger) : commitSeqNum' = s
    /\ UNCHANGED <<history, ledgerBranches>>

\* A client receives the committed status for a responded rw tx
StatusCommittedResponseAction ==
    /\ HistoryNotFull
    /\ \E i \in HIdx :
        /\ IsRwResp(i)
        /\ history[i].tx_id[2] <= commitSeqNum
        /\ ~ \E j \in HIdx : IsStatus(j) /\ history[j].tx_id = history[i].tx_id
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Once the bounded history is exhausted and nothing else can happen, stutter
HistoryExhausted ==
    /\ ~ HistoryNotFull
    /\ UNCHANGED vars

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ CommitAction
    \/ StatusCommittedResponseAction
    \/ HistoryExhausted

Fairness ==
    /\ WF_vars(RwTxExecuteAction)
    /\ WF_vars(RwTxResponseAction)
    /\ WF_vars(RoTxResponseAction)
    /\ WF_vars(CommitAction)
    /\ WF_vars(StatusCommittedResponseAction)

SpecSingleNode == Init /\ [][Next]_vars /\ Fairness

MCSpecSingleNode == SpecSingleNode

-----------------------------------------------------------------------------
\* Invariants

HistoryBoundInv == Len(history) <= HistoryLimit

TypeOK ==
    /\ \A i \in HIdx :
        history[i].type \in {RwTxRequest, RwTxResponse, RoTxRequest,
                             RoTxResponse, TxStatusReceived}
    /\ \A i \in HIdx : IsStatus(i) => history[i].status \in {CommittedStatus, InvalidStatus}
    /\ commitSeqNum \in 0..Len(Ledger)

\* Every response is preceded by a matching request of the same kind
AllReceivedIsFirstSentInv ==
    \A j \in HIdx :
        /\ IsRwResp(j) => \E i \in 1..(j-1) : IsRwReq(i) /\ history[i].tx = history[j].tx
        /\ IsRoResp(j) => \E i \in 1..(j-1) : IsRoReq(i) /\ history[i].tx = history[j].tx

\* Responses that come after a committed status (and are at or beyond its
\* position in the serial order) observe the committed tx
AllCommittedObservedInv ==
    \A i, j \in HIdx :
        ( /\ IsCommitted(i)
          /\ IsResp(j)
          /\ i < j
          /\ history[j].tx_id[2] >= history[i].tx_id[2] )
        => TxsOfTxIds({history[i].tx_id}) \subseteq Range(history[j].observed)

\* Only transactions that were requested (rw) can be observed
OnlyObserveSentRequestsInv ==
    \A j \in HIdx :
        IsResp(j) =>
            \A t \in Range(history[j].observed) :
                \E i \in 1..(j-1) : IsRwReq(i) /\ history[i].tx = t

\* Request identifiers are unique, and each request gets at most one response
UniqueTxsInv ==
    /\ \A i, j \in HIdx :
        ( (IsRwReq(i) \/ IsRoReq(i)) /\ (IsRwReq(j) \/ IsRoReq(j))
          /\ history[i].tx = history[j].tx ) => i = j
    /\ \A i, j \in HIdx :
        (IsResp(i) /\ IsResp(j) /\ history[i].tx = history[j].tx) => i = j

\* Distinct rw responses carry distinct tx ids
UniqueTxIdsInv ==
    \A i, j \in HIdx :
        (IsRwResp(i) /\ IsRwResp(j) /\ history[i].tx_id = history[j].tx_id) => i = j

\* Distinct rw responses carry distinct sequence numbers
UniqueSeqNumsInv ==
    \A i, j \in HIdx :
        (IsRwResp(i) /\ IsRwResp(j) /\ history[i].tx_id[2] = history[j].tx_id[2]) => i = j

\* A tx id is never both committed and invalid, and statuses refer to known txs
CommittedOrInvalidStrongInv ==
    /\ CommittedTxIds \cap InvalidTxIds = {}
    /\ \A i \in HIdx :
        IsStatus(i) =>
            \E j \in 1..(i-1) : IsRwResp(j) /\ history[j].tx_id = history[i].tx_id

\* Rw responses are consistent with a single serial order
SerialRespSet(S) ==
    /\ \A i \in S :
        /\ Len(history[i].observed) = history[i].tx_id[2]
        /\ Len(history[i].observed) > 0
        /\ history[i].observed[Len(history[i].observed)] = history[i].tx
    /\ \A i, j \in S :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

RwSerializableInv ==
    SerialRespSet({ i \in HIdx : IsRwResp(i) })

CommittedRwSerializableInv ==
    SerialRespSet(CommittedRwRespIdx)

\* Transactions reported invalid are never observed
InvalidNotObservedInv ==
    \A j \in HIdx :
        IsResp(j) => TxsOfTxIds(InvalidTxIds) \cap Range(history[j].observed) = {}

InvalidNotObservedByCommittedInv ==
    \A j \in CommittedRwRespIdx :
        TxsOfTxIds(InvalidTxIds) \cap Range(history[j].observed) = {}

\* Each tx is observed at most once within any response
AtMostOnceObservedInv ==
    \A j \in HIdx :
        IsResp(j) =>
            \A a, b \in DOMAIN history[j].observed :
                history[j].observed[a] = history[j].observed[b] => a = b

\* Ledger well-formedness: no dangling references
LedgerConsistentInv ==
    /\ \A s \in DOMAIN Ledger : \E i \in HIdx : IsRwReq(i) /\ history[i].tx = Ledger[s]
    /\ \A a, b \in DOMAIN Ledger : Ledger[a] = Ledger[b] => a = b

-----------------------------------------------------------------------------
\* Liveness (bounded progress)

ExecutedEventuallyRespondedProp ==
    \A t \in 1..HistoryLimit :
        (t \in Range(Ledger)) ~> (t \in RespondedTxs \/ ~HistoryNotFull)

CommittedEventuallyNotifiedProp ==
    \A s \in 1..HistoryLimit :
        (s <= commitSeqNum /\ \E i \in HIdx : IsRwResp(i) /\ history[i].tx_id[2] = s)
            ~> ((<<FirstBranch, s>> \in CommittedTxIds) \/ ~HistoryNotFull)

=============================================================================