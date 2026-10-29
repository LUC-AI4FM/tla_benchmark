---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Bounds used to keep the state space finite for model checking
RequestLimit == 2
OtherTxnLimit == 1

\* External event types
RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"

TxStatuses == {CommittedStatus, InvalidStatus}

Views == Nat
SeqNums == Nat
TxIDs == Views \X SeqNums
Txs == Nat

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* Helpers
Last(s) == s[Len(s)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* The transaction ids contained in a ledger, skipping entries without txs
RECURSIVE TxsOf(_)
TxsOf(s) ==
    IF s = <<>> THEN <<>>
    ELSE (IF "tx" \in DOMAIN Head(s) THEN <<Head(s).tx>> ELSE <<>>) \o TxsOf(Tail(s))

RequestIndices == {i \in DOMAIN history : history[i].type = RwTxRequest}

NumRequests == Cardinality(RequestIndices)

NumOtherTxns ==
    Cardinality({ <<v, s>> \in (DOMAIN ledgerBranches) \X Nat :
                    /\ s \in DOMAIN ledgerBranches[v]
                    /\ ~("tx" \in DOMAIN ledgerBranches[v][s]) })

\* Type invariants
LedgerTypeOK ==
    \A view \in DOMAIN ledgerBranches :
        \A seqnum \in DOMAIN ledgerBranches[view] :
            /\ ledgerBranches[view][seqnum].view \in Views
            /\ "tx" \in DOMAIN ledgerBranches[view][seqnum]
                => ledgerBranches[view][seqnum].tx \in Txs

HistoryTypeOK ==
    \A i \in DOMAIN history :
        \/ /\ history[i].type = RwTxRequest
           /\ history[i].tx \in Txs
        \/ /\ history[i].type = RwTxResponse
           /\ history[i].tx \in Txs
           /\ history[i].tx_id \in TxIDs
           /\ history[i].observed \in Seq(Txs)
        \/ /\ history[i].type = TxStatusReceived
           /\ history[i].tx_id \in TxIDs
           /\ history[i].status \in TxStatuses

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RwTxResponse, TxStatusReceived}] \cup
                       [type : {RwTxRequest}, tx : Txs] \cup
                       [type : {RwTxResponse}, tx : Txs, tx_id : TxIDs, observed : Seq(Txs)] \cup
                       [type : {TxStatusReceived}, tx_id : TxIDs, status : TxStatuses])
    /\ HistoryTypeOK
    /\ LedgerTypeOK

\* Initial state: a single node in view 1 with an empty ledger
Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..1 |-> <<>>]

\* Submit a new read-write transaction request with a unique identifier
RwTxRequestAction ==
    /\ NumRequests < RequestLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NumRequests])
    /\ UNCHANGED ledgerBranches

\* Execute a pending request by appending it to some ledger branch
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A view \in DOMAIN ledgerBranches :
             \A seqnum \in DOMAIN ledgerBranches[view] :
                 "tx" \in DOMAIN ledgerBranches[view][seqnum]
                     => ledgerBranches[view][seqnum].tx # history[i].tx
        /\ \E view \in DOMAIN ledgerBranches :
             ledgerBranches' = [ledgerBranches EXCEPT ![view] =
                                    Append(@, [view |-> view, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to an executed request which has not yet been responded to
RwTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN history :
             ~(history[j].type = RwTxResponse /\ history[j].tx = history[i].tx)
        /\ \E view \in DOMAIN ledgerBranches :
             \E seqnum \in DOMAIN ledgerBranches[view] :
                 /\ "tx" \in DOMAIN ledgerBranches[view][seqnum]
                 /\ ledgerBranches[view][seqnum].tx = history[i].tx
                 /\ history' = Append(history,
                        [type |-> RwTxResponse,
                         tx |-> history[i].tx,
                         observed |-> TxsOf(SubSeq(ledgerBranches[view], 1, seqnum)),
                         tx_id |-> <<ledgerBranches[view][seqnum].view, seqnum>>])
    /\ UNCHANGED ledgerBranches

\* Issue a committed status for a transaction in the highest view's ledger
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(Last(ledgerBranches)) >= history[i].tx_id[2]
        /\ Last(ledgerBranches)[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ "tx" \in DOMAIN Last(ledgerBranches)[history[i].tx_id[2]]
        /\ Last(ledgerBranches)[history[i].tx_id[2]].tx = history[i].tx
        /\ \A j \in DOMAIN history :
             ~(/\ history[j].type = TxStatusReceived
               /\ history[j].tx_id = history[i].tx_id
               /\ history[j].status \in {InvalidStatus, CommittedStatus})
        /\ history' = Append(history,
               [type |-> TxStatusReceived,
                tx_id |-> history[i].tx_id,
                status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Append ledger entries without associated transactions (other activity)
AppendOtherTxnAction ==
    /\ NumOtherTxns < OtherTxnLimit
    /\ \E view \in DOMAIN ledgerBranches :
         ledgerBranches' = [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

SpecSingleNode == Init /\ [][Next]_vars

\* Each ledger branch is append-only
LedgersMonoProp ==
    [][/\ DOMAIN ledgerBranches \subseteq DOMAIN ledgerBranches'
       /\ \A view \in DOMAIN ledgerBranches :
            IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_vars

=============================================================================