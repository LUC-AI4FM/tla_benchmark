---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Bound on the length of the external history (used only as a state constraint
\* for model checking; it does not restrict the behaviours in Spec).
CONSTANT HistoryLimit

ASSUME HistoryLimit \in Nat

\* External history of requests and responses observed by clients
VARIABLE history

\* Abstract ledgers that contain only client transactions (no signatures).
\* Indexed by view; each ledger is the ledger associated with the leader of
\* that view. With a single node there are no view changes, so only view 1.
VARIABLE ledgerBranches

vars == << history, ledgerBranches >>

-----------------------------------------------------------------------------
\* Constants describing the external history

RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"
TxStatuses       == {CommittedStatus, InvalidStatus}

EventTypes == {RwTxRequest, RwTxResponse, TxStatusReceived}

Views == Nat \ {0}
SeqNums == Nat \ {0}
Txs == Nat
TxIDs == Views \X SeqNums

-----------------------------------------------------------------------------
\* Helper operators

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A k \in 1..Len(s) : s[k] = t[k]

Last(s) == s[Len(s)]

RequestIndices == {i \in DOMAIN history : history[i].type = RwTxRequest}

\* Fresh, unique identifier for the next request
NextRequestId == Cardinality(RequestIndices)

\* Transactions observed in the ledger up to and including index i
ObservedTxs(ledger, i) ==
    LET entries == SelectSeq(SubSeq(ledger, 1, i), LAMBDA e : "tx" \in DOMAIN e)
    IN  [k \in 1..Len(entries) |-> entries[k].tx]

-----------------------------------------------------------------------------
\* Type correctness

HistTypeOK ==
    /\ history \in Seq([type : EventTypes] \cup
                       [type : {RwTxRequest}, tx : Txs] \cup
                       [type : {RwTxResponse}, tx : Txs,
                        observed : Seq(Txs), tx_id : TxIDs] \cup
                       [type : {TxStatusReceived}, tx_id : TxIDs,
                        status : TxStatuses])
    /\ \A i \in DOMAIN history :
        /\ history[i].type \in EventTypes
        /\ history[i].type = RwTxRequest =>
            /\ DOMAIN history[i] = {"type", "tx"}
            /\ history[i].tx \in Txs
        /\ history[i].type = RwTxResponse =>
            /\ DOMAIN history[i] = {"type", "tx", "observed", "tx_id"}
            /\ history[i].tx \in Txs
            /\ history[i].observed \in Seq(Txs)
            /\ history[i].tx_id \in TxIDs
        /\ history[i].type = TxStatusReceived =>
            /\ DOMAIN history[i] = {"type", "tx_id", "status"}
            /\ history[i].tx_id \in TxIDs
            /\ history[i].status \in TxStatuses

LedgerTypeOK ==
    /\ DOMAIN ledgerBranches \subseteq Views
    /\ \A view \in DOMAIN ledgerBranches :
        /\ ledgerBranches[view] \in Seq([view : Views] \cup [view : Views, tx : Txs])
        /\ \A seqnum \in DOMAIN ledgerBranches[view] :
            \* Each ledger entry is a record containing a view and optionally a tx;
            \* the ledger entry index is the sequence number
            /\ ledgerBranches[view][seqnum].view \in Views
            /\ "tx" \in DOMAIN ledgerBranches[view][seqnum] =>
                    ledgerBranches[view][seqnum].tx \in Txs

TypeOK ==
    /\ HistTypeOK
    /\ LedgerTypeOK

\* In this abstract version of CCF's consensus layer, each ledger is append-only
LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches :
          IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = << >>
    /\ ledgerBranches = [x \in 1..1 |-> << >>]

-----------------------------------------------------------------------------
\* Actions

\* Submit a new read-write transaction
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        \* Check transaction has not already been added to a ledger
        /\ \A view \in DOMAIN ledgerBranches :
            \A seqnum \in DOMAIN ledgerBranches[view] :
                "tx" \in DOMAIN ledgerBranches[view][seqnum]
                    => history[i].tx /= ledgerBranches[view][seqnum].tx
        \* Single node, single view: append to the ledger of view 1
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![1] =
                                Append(@, [view |-> 1, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to a read-write transaction
RwTxResponseAction ==
    /\ \E i \in DOMAIN ledgerBranches[1] :
        \* Request has been received and executed but not yet responded to
        /\ "tx" \in DOMAIN ledgerBranches[1][i]
        /\ \E j \in DOMAIN history :
            /\ history[j].type = RwTxRequest
            /\ history[j].tx = ledgerBranches[1][i].tx
        /\ ~ \E j \in DOMAIN history :
            /\ history[j].type = RwTxResponse
            /\ history[j].tx = ledgerBranches[1][i].tx
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> ledgerBranches[1][i].tx,
               observed |-> ObservedTxs(ledgerBranches[1], i),
               tx_id    |-> << ledgerBranches[1][i].view, i >>])
    /\ UNCHANGED ledgerBranches

\* Report the committed status of a transaction which has been responded to.
\* With a single node, every transaction in the ledger is committed.
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(ledgerBranches[1]) >= history[i].tx_id[2]
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx_id  |-> history[i].tx_id,
               status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Append a transaction to the ledger which does not impact the state considered
AppendOtherTxnAction ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![1] = Append(@, [view |-> 1])]
    /\ UNCHANGED history

-----------------------------------------------------------------------------
\* Specification

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

\* State constraint for bounded model checking
StateConstraint ==
    /\ Len(history) <= HistoryLimit
    /\ Len(ledgerBranches[1]) <= HistoryLimit

-----------------------------------------------------------------------------
\* Properties

THEOREM Spec => []TypeOK
THEOREM Spec => LedgersMonoProp

=============================================================================