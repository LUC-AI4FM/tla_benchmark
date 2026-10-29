---- MODULE MCMultiNode ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANT FirstBranch
CONSTANTS HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

Range(s) == {s[k] : k \in DOMAIN s}

LastBranch == ledgerBranches[Len(ledgerBranches)]

CurrentView == FirstBranch + Len(ledgerBranches) - 1

RwRequestIdx  == {i \in DOMAIN history : history[i].type = RwTxRequest}
RoRequestIdx  == {i \in DOMAIN history : history[i].type = RoTxRequest}
RwResponseIdx == {i \in DOMAIN history : history[i].type = RwTxResponse}
RoResponseIdx == {i \in DOMAIN history : history[i].type = RoTxResponse}
ResponseIdx   == RwResponseIdx \cup RoResponseIdx
StatusIdx     == {i \in DOMAIN history : history[i].type = TxStatusReceived}

CommittedStatusIdx == {i \in StatusIdx : history[i].status = CommittedStatus}
InvalidStatusIdx   == {i \in StatusIdx : history[i].status = InvalidStatus}

ResponseTxIds == {history[i].tx_id : i \in ResponseIdx}

CommittedTxIds == {history[i].tx_id : i \in CommittedStatusIdx}
InvalidTxIds   == {history[i].tx_id : i \in InvalidStatusIdx}

CommittedRwIdx == {i \in RwResponseIdx : history[i].tx_id \in CommittedTxIds}
CommittedIdx   == {i \in ResponseIdx : history[i].tx_id \in CommittedTxIds}

CommittedSeqNums == {t[2] : t \in CommittedTxIds}

CommittedIndex ==
    IF CommittedSeqNums = {} THEN 0
    ELSE CHOOSE m \in CommittedSeqNums : \A n \in CommittedSeqNums : n <= m

InLastBranch(t) ==
    /\ t[2] \in DOMAIN LastBranch
    /\ LastBranch[t[2]].view = t[1]

StatusExists(t, st) ==
    \E j \in StatusIdx : history[j].tx_id = t /\ history[j].status = st

InAnyBranch(tx) ==
    \E b \in 1..Len(ledgerBranches) :
        \E k \in DOMAIN ledgerBranches[b] : ledgerBranches[b][k].tx = tx

\* ---------------------------------------------------------------------------
\* Single node behaviour
\* ---------------------------------------------------------------------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    \E i \in RwRequestIdx :
        /\ ~InAnyBranch(history[i].tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
        /\ UNCHANGED history

RwTxResponseAction ==
    \E s \in DOMAIN LastBranch :
        /\ \A j \in RwResponseIdx : history[j].tx # LastBranch[s].tx
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> LastBranch[s].tx,
                 observed |-> [k \in 1..s |-> LastBranch[k].tx],
                 tx_id |-> <<LastBranch[s].view, s>>])
        /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    \E i \in RoRequestIdx :
        /\ \A j \in RoResponseIdx : history[j].tx # history[i].tx
        /\ Len(LastBranch) > 0
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [k \in 1..Len(LastBranch) |-> LastBranch[k].tx],
                 tx_id |-> <<LastBranch[Len(LastBranch)].view, Len(LastBranch)>>])
        /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    \E t \in ResponseTxIds :
        /\ InLastBranch(t)
        /\ ~StatusExists(t, CommittedStatus)
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> t, status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction

SpecSingleNode == Init /\ [][NextSingleNodeAction]_vars

\* ---------------------------------------------------------------------------
\* Multi node behaviour
\* ---------------------------------------------------------------------------

\* View change: start a new branch from a prefix of the current branch,
\* never truncating committed entries.
TruncateLedgerAction ==
    \E i \in CommittedIndex..Len(LastBranch) :
        /\ ledgerBranches' = Append(ledgerBranches, SubSeq(LastBranch, 1, i))
        /\ UNCHANGED history

\* A transaction ID is invalid if it is from an older view and is not
\* present in the current branch (it can then never become committed).
StatusInvalidResponseAction ==
    \E t \in ResponseTxIds :
        /\ t[1] < CurrentView
        /\ ~InLastBranch(t)
        /\ ~StatusExists(t, InvalidStatus)
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> t, status |-> InvalidStatus])
        /\ UNCHANGED ledgerBranches

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

SpecMultiNode == Init /\ [][NextMultiNodeAction]_vars

\* ---------------------------------------------------------------------------
\* Bounded model checking
\* ---------------------------------------------------------------------------

MCHistoryAction ==
    /\ Len(history) < HistoryLimit
    /\ \/ RwTxRequestAction
       \/ RwTxResponseAction
       \/ RoTxRequestAction
       \/ RoTxResponseAction
       \/ StatusCommittedResponseAction
       \/ StatusInvalidResponseAction

MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

MCNextMultiNodeAction ==
    \/ MCHistoryAction
    \/ RwTxExecuteAction
    \/ MCTruncateLedgerAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

AllReceivedIsFirstSentInv ==
    /\ \A i \in RwResponseIdx :
        \E j \in 1..(i - 1) :
            history[j].type = RwTxRequest /\ history[j].tx = history[i].tx
    /\ \A i \in RoResponseIdx :
        \E j \in 1..(i - 1) :
            history[j].type = RoTxRequest /\ history[j].tx = history[i].tx
    /\ \A i \in StatusIdx :
        \E j \in 1..(i - 1) :
            /\ history[j].type \in {RwTxResponse, RoTxResponse}
            /\ history[j].tx_id = history[i].tx_id

AllCommittedObservedInv ==
    \A i, j \in CommittedIdx :
        (i \in RwResponseIdx /\ history[i].tx_id[2] <= history[j].tx_id[2])
            => history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in ResponseIdx :
        \A tx \in Range(history[i].observed) :
            \E j \in RwRequestIdx : history[j].tx = tx

UniqueTxsInv ==
    /\ \A i, j \in RwResponseIdx : history[i].tx = history[j].tx => i = j
    /\ \A i, j \in RoResponseIdx : history[i].tx = history[j].tx => i = j

SameObservationsInv ==
    \A i, j \in ResponseIdx :
        history[i].tx_id = history[j].tx_id
            => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in RwResponseIdx :
        history[i].tx_id = history[j].tx_id => i = j

UniqueTxRequestsInv ==
    \A i, j \in RwRequestIdx \cup RoRequestIdx :
        history[i].tx = history[j].tx => i = j

UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRwIdx :
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

CommittedOrInvalidStrongInv ==
    /\ CommittedTxIds \cap InvalidTxIds = {}
    /\ \A i, j \in StatusIdx :
        history[i].tx_id = history[j].tx_id
            => history[i].status = history[j].status

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwIdx :
        history[i].tx_id[2] <= history[j].tx_id[2]
            => /\ Len(history[i].observed) <= Len(history[j].observed)
               /\ history[i].observed =
                    SubSeq(history[j].observed, 1, Len(history[i].observed))

InvalidNotObservedByCommittedInv ==
    \A i \in RwResponseIdx :
        history[i].tx_id \in InvalidTxIds
            => \A j \in CommittedIdx :
                    history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in ResponseIdx :
        \A a, b \in DOMAIN history[i].observed :
            history[i].observed[a] = history[i].observed[b] => a = b

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwIdx :
        (\E k \in RwRequestIdx : history[k].tx = history[j].tx /\ i < k)
            => history[i].tx_id[2] < history[j].tx_id[2]

====