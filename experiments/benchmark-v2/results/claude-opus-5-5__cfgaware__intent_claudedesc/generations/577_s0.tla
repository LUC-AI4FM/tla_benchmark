---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    FirstBranch,
    HistoryLimit,
    ViewLimit,
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------- Helpers ----------------

Range(s) == {s[i] : i \in DOMAIN s}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

CurrentView == Len(ledgerBranches)

Latest == ledgerBranches[Len(ledgerBranches)]

BranchTxs(b) == {b[i].tx : i \in DOMAIN b}

ReqIdx == {i \in DOMAIN history : history[i].type = RwTxRequest}

RespIdx == {i \in DOMAIN history : history[i].type = RwTxResponse}

StatusIdx == {i \in DOMAIN history : history[i].type = TxStatusReceived}

RequestedTxs == {history[i].tx : i \in ReqIdx}

RespondedTxs == {history[i].tx : i \in RespIdx}

HasStatus(tid, s) ==
    \E k \in StatusIdx : history[k].tx_id = tid /\ history[k].status = s

HasAnyStatus(tid) ==
    \E k \in StatusIdx : history[k].tx_id = tid

CommittedRespIdx == {i \in RespIdx : HasStatus(history[i].tx_id, CommittedStatus)}

InvalidRespIdx == {i \in RespIdx : HasStatus(history[i].tx_id, InvalidStatus)}

CommitLen ==
    Max({history[k].tx_id[2] : k \in {j \in StatusIdx : history[j].status = CommittedStatus}} \cup {0})

\* ---------------- Initial states ----------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

\* Alternative initial state: mid-execution with two branches and committed txs
InitAlt ==
    /\ history = <<
         [type |-> RwTxRequest, tx |-> 1],
         [type |-> RwTxRequest, tx |-> 2],
         [type |-> RwTxResponse, tx |-> 1, tx_id |-> <<1, 1>>, observed |-> <<>>],
         [type |-> RwTxResponse, tx |-> 2, tx_id |-> <<1, 2>>, observed |-> <<1>>],
         [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus]
       >>
    /\ ledgerBranches = <<
         << [view |-> 1, tx |-> 1], [view |-> 1, tx |-> 2] >>,
         << [view |-> 1, tx |-> 1] >>
       >>

\* ---------------- Actions ----------------

\* Client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* Primary executes a requested transaction, appending it to the current branch
RwTxExecuteAction ==
    /\ \E t \in RequestedTxs :
        /\ \A b \in 1..Len(ledgerBranches) : t \notin BranchTxs(ledgerBranches[b])
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                                Append(@, [view |-> CurrentView, tx |-> t])]
    /\ UNCHANGED history

\* Client receives a response with tx id and observed prior transactions
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN Latest :
        /\ Latest[i].tx \notin RespondedTxs
        /\ history' = Append(history,
              [type |-> RwTxResponse,
               tx |-> Latest[i].tx,
               tx_id |-> <<Latest[i].view, i>>,
               observed |-> [k \in 1..(i - 1) |-> Latest[k].tx]])
    /\ UNCHANGED ledgerBranches

\* Client learns a transaction committed
StatusCommittedAction ==
    /\ Len(history) < HistoryLimit
    /\ \E r \in RespIdx :
        LET tid == history[r].tx_id IN
        /\ ~HasAnyStatus(tid)
        /\ tid[2] <= Len(Latest)
        /\ Latest[tid[2]].view = tid[1]
        /\ history' = Append(history,
              [type |-> TxStatusReceived, tx_id |-> tid, status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Client learns a transaction is invalid (lost in a view change)
StatusInvalidAction ==
    /\ Len(history) < HistoryLimit
    /\ \E r \in RespIdx :
        LET tid == history[r].tx_id IN
        /\ ~HasAnyStatus(tid)
        /\ CurrentView > tid[1]
        /\ \/ Len(Latest) < tid[2]
           \/ Latest[tid[2]].view # tid[1]
        /\ history' = Append(history,
              [type |-> TxStatusReceived, tx_id |-> tid, status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* View change: new branch forks from a prefix of the latest branch
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E k \in CommitLen..Len(Latest) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, k))
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedAction
    \/ StatusInvalidAction
    \/ TruncateLedgerAction

SpecMultiNodeReads == Init /\ [][Next]_vars

MCSpecMultiNodeReadsAlt == InitAlt /\ [][Next]_vars

\* ---------------- Invariants ----------------

AllReceivedIsFirstSentInv ==
    \A i \in RespIdx :
        \E j \in 1..(i - 1) :
            history[j].type = RwTxRequest /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in CommittedRespIdx :
        history[i].tx_id[2] < history[j].tx_id[2]
            => history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in RespIdx :
        \A k \in DOMAIN history[i].observed :
            \E j \in 1..(i - 1) :
                history[j].type = RwTxRequest /\ history[j].tx = history[i].observed[k]

UniqueTxsInv ==
    \A b \in 1..Len(ledgerBranches) :
        \A x, y \in DOMAIN ledgerBranches[b] :
            ledgerBranches[b][x].tx = ledgerBranches[b][y].tx => x = y

SameObservationsInv ==
    \A i, j \in RespIdx :
        history[i].tx_id = history[j].tx_id =>
            /\ history[i].observed = history[j].observed
            /\ history[i].tx = history[j].tx

UniqueTxIdsInv ==
    \A i, j \in RespIdx :
        (history[i].tx # history[j].tx) => (history[i].tx_id # history[j].tx_id)

UniqueTxRequestsInv ==
    \A i, j \in ReqIdx :
        i # j => history[i].tx # history[j].tx

UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRespIdx :
        history[i].tx_id[2] = history[j].tx_id[2] => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i \in RespIdx :
        ~(HasStatus(history[i].tx_id, CommittedStatus)
          /\ HasStatus(history[i].tx_id, InvalidStatus))

CommittedRwSerializableInv ==
    \A i, j \in CommittedRespIdx :
        LET oi == history[i].observed
            oj == history[j].observed
        IN history[i].tx_id[2] < history[j].tx_id[2] =>
            /\ Len(oi) < Len(oj)
            /\ SubSeq(oj, 1, Len(oi)) = oi
            /\ oj[Len(oi) + 1] = history[i].tx

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRespIdx :
        \A j \in CommittedRespIdx :
            history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in RespIdx :
        \A x, y \in DOMAIN history[i].observed :
            history[i].observed[x] = history[i].observed[y] => x = y

=============================================================================