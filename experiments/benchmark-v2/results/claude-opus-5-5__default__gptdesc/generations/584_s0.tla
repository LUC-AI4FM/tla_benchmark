---------------------------- MODULE SingleNodeReads ----------------------------
\* SingleNode extended with read-only transactions. The base SingleNode
\* definitions are inlined so the module stands alone.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxs,          \* Identifiers of read-write transactions
    RoTxs,          \* Identifiers of read-only transactions
    HistoryLimit    \* Bound on the length of the client-observed history

ASSUME RwTxs \cap RoTxs = {}
ASSUME HistoryLimit \in Nat

\* Event types recorded in the client-observed history
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
RoTxRequest      == "RoTxRequest"
RoTxResponse     == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus  == "CommittedStatus"

VARIABLES
    history,        \* Sequence of client events (requests and responses)
    ledgerBranches  \* Ledger branches, indexed by view

vars == <<history, ledgerBranches>>

Last(s) == s[Len(s)]

\* A single node only ever has one view, so there is one ledger branch
Views == 1..1

LedgerEntries == [view : Views, tx : RwTxs]

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : RwTxs \cup RoTxs]
                       \cup [type : {RwTxResponse, RoTxResponse},
                             tx : RwTxs \cup RoTxs,
                             observed : Seq(RwTxs),
                             tx_id : Views \X Nat]
                       \cup [type : {TxStatusReceived},
                             tx_id : Views \X Nat,
                             status : {CommittedStatus}])
    /\ ledgerBranches \in [Views -> Seq(LedgerEntries)]

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in Views |-> <<>>]

-----------------------------------------------------------------------------
\* SingleNode actions

\* Submit a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ \E t \in RwTxs :
        /\ \A k \in DOMAIN history :
            history[k].type = RwTxRequest => history[k].tx /= t
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> t])
    /\ UNCHANGED ledgerBranches

\* Execute a requested read-write transaction by appending it to the ledger
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN ledgerBranches[1] :
            ledgerBranches[1][j].tx /= history[i].tx
        /\ ledgerBranches' =
            [ledgerBranches EXCEPT ![1] =
                Append(@, [view |-> 1, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to an executed read-write transaction
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN ledgerBranches[1] :
        LET b == ledgerBranches[1]
            t == b[i].tx
        IN
        /\ \A k \in DOMAIN history :
            history[k].type = RwTxResponse => history[k].tx /= t
        /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> t,
                 observed |-> [s \in 1..i |-> b[s].tx],
                 tx_id    |-> <<b[i].view, i>>])
    /\ UNCHANGED ledgerBranches

\* On a single node, any transaction in the ledger is committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id[2] <= Len(ledgerBranches[1])
        /\ \A k \in DOMAIN history :
            history[k].type = TxStatusReceived
                => history[k].tx_id /= history[i].tx_id
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction

SpecSingleNode == Init /\ [][NextSingleNodeAction]_vars

-----------------------------------------------------------------------------
\* Read-only transaction extension

\* Submit a new read-only transaction request
RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ \E t \in RoTxs :
        /\ \A k \in DOMAIN history :
            history[k].type = RoTxRequest => history[k].tx /= t
        /\ history' = Append(history, [type |-> RoTxRequest, tx |-> t])
    /\ UNCHANGED ledgerBranches

\* Respond to a read-only transaction request.
\* Read-only transactions are assumed to always be forwarded.
\* The read and the response happen in one atomic step.
RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A k \in DOMAIN history :
            history[k].type = RoTxResponse => history[k].tx /= history[i].tx
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(history,
                    [type     |-> RoTxResponse,
                     tx       |-> history[i].tx,
                     observed |-> [s \in DOMAIN ledgerBranches[view] |->
                                      ledgerBranches[view][s].tx],
                     tx_id    |-> <<Last(ledgerBranches[view]).view,
                                    Len(ledgerBranches[view])>>])
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

Next == NextSingleNodeReadsAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

Spec == SpecSingleNodeReads

-----------------------------------------------------------------------------
\* Safety invariants

\* Every read-only response answers a previously submitted read-only request
RoResponseHasRequestInv ==
    \A k \in DOMAIN history :
        history[k].type = RoTxResponse =>
            \E j \in 1..(k-1) :
                /\ history[j].type = RoTxRequest
                /\ history[j].tx = history[k].tx

\* Each read-only transaction receives at most one response
AtMostOneRoResponseInv ==
    \A j, k \in DOMAIN history :
        (/\ history[j].type = RoTxResponse
         /\ history[k].type = RoTxResponse
         /\ history[j].tx = history[k].tx) => j = k

\* Read-only responses only observe read-write transactions from the ledger
RoObservesOnlyRwInv ==
    \A k \in DOMAIN history :
        history[k].type = RoTxResponse =>
            \A s \in DOMAIN history[k].observed : history[k].observed[s] \in RwTxs

=============================================================================