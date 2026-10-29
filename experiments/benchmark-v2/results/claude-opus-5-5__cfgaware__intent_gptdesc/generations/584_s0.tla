---------------------------- MODULE SingleNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Model bounds and event-type tags (overridable from the configuration)
HistoryLimit == 6
ViewLimit == 2

RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest == "RoTxRequest"
RoTxResponse == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

Views == 1..ViewLimit
SeqNums == 1..HistoryLimit
TxIDs == Views \X SeqNums
RequestIds == 1..HistoryLimit

RequestTypes == {RwTxRequest, RoTxRequest}

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Range(f) == {f[x] : x \in DOMAIN f}

LatestView == Len(ledgerBranches)
Latest == ledgerBranches[LatestView]

NumRequests == Cardinality({i \in DOMAIN history : history[i].type \in RequestTypes})
NextRequestId == NumRequests + 1

IsRequest(i, t) == history[i].type = t
IsResponse(i, t) == history[i].type = t

Responded(t, rid) ==
    \E k \in DOMAIN history : history[k].type = t /\ history[k].tx = rid

ExecutedInAnyBranch(rid) ==
    \E v \in DOMAIN ledgerBranches :
        \E s \in DOMAIN ledgerBranches[v] : ledgerBranches[v][s].tx = rid

CommittedTxIDs ==
    {history[k].tx_id : k \in {j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].status = CommittedStatus}}

CommittedIndex ==
    IF CommittedTxIDs = {} THEN 0
    ELSE Max({t[2] : t \in CommittedTxIDs})

StatusReported(tid) ==
    \E k \in DOMAIN history :
        history[k].type = TxStatusReceived /\ history[k].tx_id = tid

ObservedTxs(branch, upto) == [s \in 1..upto |-> branch[s].tx]

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

\* ---------------------------------------------------------------------------
\* Read-write transactions
\* ---------------------------------------------------------------------------

RwTxRequestAction ==
    /\ NumRequests < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute (commit to the ledger) a received read-write request
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRequest(i, RwTxRequest)
        /\ ~ExecutedInAnyBranch(history[i].tx)
        /\ ledgerBranches' =
               [ledgerBranches EXCEPT ![LatestView] =
                    Append(@, [view |-> LatestView, tx |-> history[i].tx])]
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ \E s \in DOMAIN Latest :
        /\ ~Responded(RwTxResponse, Latest[s].tx)
        /\ history' = Append(history,
               [type |-> RwTxResponse,
                tx |-> Latest[s].tx,
                observed |-> ObservedTxs(Latest, s),
                tx_id |-> <<Latest[s].view, s>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ IsResponse(i, RwTxResponse)
        /\ LET tid == history[i].tx_id IN
            /\ ~StatusReported(tid)
            /\ tid[2] \in DOMAIN Latest
            /\ Latest[tid[2]].view = tid[1]
            /\ history' = Append(history,
                   [type |-> TxStatusReceived, tx_id |-> tid,
                    status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ IsResponse(i, RwTxResponse)
        /\ LET tid == history[i].tx_id IN
            /\ ~StatusReported(tid)
            /\ \/ /\ tid[2] \in DOMAIN Latest
                  /\ Latest[tid[2]].view # tid[1]
               \/ /\ tid[2] \notin DOMAIN Latest
                  /\ LatestView > tid[1]
            /\ history' = Append(history,
                   [type |-> TxStatusReceived, tx_id |-> tid,
                    status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* Start a new view, keeping a prefix of the latest branch that contains
\* at least everything reported as committed.
TruncateLedgerAction ==
    /\ LatestView < ViewLimit
    /\ \E i \in CommittedIndex..Len(Latest) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, i))
    /\ UNCHANGED history

\* ---------------------------------------------------------------------------
\* Read-only transactions
\* ---------------------------------------------------------------------------

RoTxRequestAction ==
    /\ NumRequests < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Respond to a pending read-only request exactly once, observing a snapshot
\* of the latest ledger branch; the ledger is not modified.
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRequest(i, RoTxRequest)
        /\ ~Responded(RoTxResponse, history[i].tx)
        /\ Len(Latest) > 0
        /\ history' = Append(history,
               [type |-> RoTxResponse,
                tx |-> history[i].tx,
                observed |-> ObservedTxs(Latest, Len(Latest)),
                tx_id |-> <<Latest[Len(Latest)].view, Len(Latest)>>])
    /\ UNCHANGED ledgerBranches

\* ---------------------------------------------------------------------------
\* Specification
\* ---------------------------------------------------------------------------

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

Next == NextSingleNodeReadsAction

Fairness ==
    /\ WF_vars(RoTxResponseAction)
    /\ WF_vars(RwTxExecuteAction)
    /\ WF_vars(RwTxResponseAction)

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

Spec == SpecSingleNodeReads /\ Fairness

\* ---------------------------------------------------------------------------
\* Safety invariants
\* ---------------------------------------------------------------------------

LedgerEntries == [view : Views, tx : RequestIds]

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : RequestIds]
                       \cup [type : {RwTxResponse, RoTxResponse}, tx : RequestIds,
                             observed : Seq(RequestIds), tx_id : TxIDs]
                       \cup [type : {TxStatusReceived}, tx_id : TxIDs,
                             status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) \in Views

\* Entries of branch v carry views no greater than v, in non-decreasing order
LedgerBranchViewsInv ==
    \A v \in DOMAIN ledgerBranches :
        \A s \in DOMAIN ledgerBranches[v] :
            /\ ledgerBranches[v][s].view <= v
            /\ s > 1 => ledgerBranches[v][s-1].view <= ledgerBranches[v][s].view

\* Every tx appears at most once in a branch
LedgerBranchUniqueTxInv ==
    \A v \in DOMAIN ledgerBranches :
        \A s1, s2 \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][s1].tx = ledgerBranches[v][s2].tx => s1 = s2

\* Only read-write requests are ever executed into the ledger
LedgerOnlyRwTxInv ==
    \A v \in DOMAIN ledgerBranches :
        \A s \in DOMAIN ledgerBranches[v] :
            \E i \in DOMAIN history :
                /\ history[i].type = RwTxRequest
                /\ history[i].tx = ledgerBranches[v][s].tx

\* Committed transactions remain in the latest branch
CommittedPreservedInv ==
    \A tid \in CommittedTxIDs :
        /\ tid[2] \in DOMAIN Latest
        /\ Latest[tid[2]].view = tid[1]

\* No duplicate responses for the same request
NoDuplicateRoResponsesInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RoTxResponse
        /\ history[j].type = RoTxResponse
        /\ history[i].tx = history[j].tx
        => i = j

NoDuplicateRwResponsesInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[j].type = RwTxResponse
        /\ history[i].tx = history[j].tx
        => i = j

\* Each response references and follows a request of matching kind
ResponseFollowsRequestInv ==
    \A j \in DOMAIN history :
        history[j].type \in {RwTxResponse, RoTxResponse} =>
            \E i \in 1..(j-1) :
                /\ history[i].tx = history[j].tx
                /\ history[i].type =
                       IF history[j].type = RoTxResponse THEN RoTxRequest
                                                         ELSE RwTxRequest

\* Request identifiers are issued in increasing order and unique
RequestIdsOrderedInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in RequestTypes
        /\ history[j].type \in RequestTypes
        /\ i < j
        => history[i].tx < history[j].tx

\* A read-only response's tx_id identifies the last observed entry and its
\* observation is non-empty
RoResponseSnapshotWellFormedInv ==
    \A j \in DOMAIN history :
        history[j].type = RoTxResponse =>
            /\ Len(history[j].observed) > 0
            /\ history[j].tx_id[2] = Len(history[j].observed)

\* Read-only observations only contain read-write transactions
RoResponseObservesOnlyRwInv ==
    \A j \in DOMAIN history :
        history[j].type = RoTxResponse =>
            \A t \in Range(history[j].observed) :
                \E i \in DOMAIN history :
                    history[i].type = RwTxRequest /\ history[i].tx = t

\* Read-only observations are a prefix of some branch, identified by tx_id
RoResponseIsBranchSnapshotInv ==
    \A j \in DOMAIN history :
        history[j].type = RoTxResponse =>
            \E v \in DOMAIN ledgerBranches :
                /\ Len(history[j].observed) <= Len(ledgerBranches[v])
                /\ \A s \in DOMAIN history[j].observed :
                       ledgerBranches[v][s].tx = history[j].observed[s]
                /\ ledgerBranches[v][Len(history[j].observed)].view
                       = history[j].tx_id[1]

\* Read-only actions never modify the ledger
RoTxDoesNotModifyLedger ==
    [][(RoTxRequestAction \/ RoTxResponseAction) => UNCHANGED ledgerBranches]_vars

\* The ledger only changes through execution or view change
LedgerChangesOnlyViaCommits ==
    [][ledgerBranches' # ledgerBranches =>
         (RwTxExecuteAction \/ TruncateLedgerAction)]_vars

\* History is append-only
HistoryAppendOnly ==
    [][/\ Len(history') >= Len(history)
       /\ SubSeq(history', 1, Len(history)) = history]_vars

\* ---------------------------------------------------------------------------
\* Liveness
\* ---------------------------------------------------------------------------

RoRequested(rid) ==
    \E i \in DOMAIN history : history[i].type = RoTxRequest /\ history[i].tx = rid

RoResponded(rid) == Responded(RoTxResponse, rid)

\* Under fair scheduling, every read-only request is eventually answered
\* once a valid snapshot exists.
RoTxEventuallyRespondedProp ==
    \A rid \in RequestIds :
        (RoRequested(rid) /\ Len(Latest) > 0) ~> RoResponded(rid)

=============================================================================