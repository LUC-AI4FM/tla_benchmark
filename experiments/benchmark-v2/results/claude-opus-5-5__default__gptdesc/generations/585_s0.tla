---------------------------- MODULE SingleNode ----------------------------
(***************************************************************************)
(* Externally visible behaviour of a single-node CCF service.              *)
(*                                                                         *)
(* The spec tracks two things:                                             *)
(*   - an abstract external history of client requests and responses;      *)
(*   - abstract per-view ledger branches, which contain only client        *)
(*     transactions (no signatures).                                       *)
(*                                                                         *)
(* Only a single node is considered, so there are no view changes. There   *)
(* is exactly one ledger branch, for view 1.                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxRequest,       \* event tag: read-write transaction request
    RwTxResponse,      \* event tag: read-write transaction response
    TxStatusReceived,  \* event tag: transaction status received
    CommittedStatus,   \* status value: committed
    InvalidStatus      \* status value: invalid

ASSUME Cardinality({RwTxRequest, RwTxResponse, TxStatusReceived}) = 3
ASSUME CommittedStatus /= InvalidStatus

VARIABLES
    history,          \* external history of requests and responses
    ledgerBranches    \* abstract ledgers, indexed by view

vars == << history, ledgerBranches >>

-----------------------------------------------------------------------------
(* Basic domains *)

\* Views start at 1.
Views == Nat \ {0}

\* Each transaction is identified by a unique natural number.
Txs == Nat

\* Sequence numbers start at 1.
SeqNums == Nat \ {0}

\* A transaction ID is a pair: view and sequence number.
TxIDs == Views \X SeqNums

TxStatuses == {CommittedStatus, InvalidStatus}

-----------------------------------------------------------------------------
(* Helper operators *)

\* s is a prefix of t.
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

\* Ledger entries that carry a client transaction.
HasTx(e) == "tx" \in DOMAIN e

\* Client transactions in the first i entries of ledger l, in ledger order.
ObservedTxs(l, i) ==
    LET txEntries == SelectSeq(SubSeq(l, 1, i), HasTx)
    IN  [k \in 1..Len(txEntries) |-> txEntries[k].tx]

\* The next fresh request identifier.
NextRequestId ==
    Cardinality({i \in DOMAIN history : history[i].type = RwTxRequest})

-----------------------------------------------------------------------------
(* Type correctness *)

RwTxRequests ==
    [type : {RwTxRequest}, tx : Txs]

RwTxResponses ==
    [type : {RwTxResponse}, tx : Txs, observed : Seq(Txs), tx_id : TxIDs]

TxStatusReceivedEvents ==
    [type : {TxStatusReceived}, tx_id : TxIDs, status : TxStatuses]

Events == RwTxRequests \cup RwTxResponses \cup TxStatusReceivedEvents

HistTypeOK ==
    history \in Seq(Events)

\* Each ledger entry is a record containing a view and, optionally, a tx.
\* The index of the entry in the ledger is its sequence number.
LedgerTypeOK ==
    /\ DOMAIN ledgerBranches \subseteq Views
    /\ \A view \in DOMAIN ledgerBranches :
        \A seqnum \in DOMAIN ledgerBranches[view] :
            /\ ledgerBranches[view][seqnum].view \in Views
            /\ HasTx(ledgerBranches[view][seqnum])
                => ledgerBranches[view][seqnum].tx \in Txs

TypeOK ==
    /\ HistTypeOK
    /\ LedgerTypeOK

-----------------------------------------------------------------------------
(* Temporal property: each ledger branch is append-only. *)

LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches :
          IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ history = << >>
    /\ ledgerBranches = [v \in 1..1 |-> << >>]

-----------------------------------------------------------------------------
(* Actions *)

\* A client submits a new read-write transaction.
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* The node executes a requested read-write transaction. It appends the
\* transaction to the ledger of view 1, and only if no ledger already
\* contains it.
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A view \in DOMAIN ledgerBranches :
            \A seqnum \in DOMAIN ledgerBranches[view] :
                HasTx(ledgerBranches[view][seqnum])
                    => history[i].tx /= ledgerBranches[view][seqnum].tx
        /\ ledgerBranches' =
            [ledgerBranches EXCEPT ![1] =
                Append(@, [view |-> 1, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* The node responds to an executed read-write transaction. Each executed
\* transaction gets at most one response.
RwTxResponseAction ==
    /\ \E i \in DOMAIN ledgerBranches[1] :
        /\ HasTx(ledgerBranches[1][i])
        /\ \A j \in DOMAIN history :
            history[j].type = RwTxResponse
                => history[j].tx /= ledgerBranches[1][i].tx
        /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> ledgerBranches[1][i].tx,
                 observed |-> ObservedTxs(ledgerBranches[1], i),
                 tx_id    |-> << 1, i >>])
    /\ UNCHANGED ledgerBranches

\* The node reports that a responded-to transaction is committed. On a
\* single node, every transaction in the ledger counts as committed.
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(ledgerBranches[1]) >= history[i].tx_id[2]
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* The node appends a transaction unrelated to the state being modelled.
AppendOtherTxnAction ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![1] = Append(@, [view |-> 1])]
    /\ UNCHANGED history

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

THEOREM TypeCorrect == Spec => []TypeOK
THEOREM LedgersMonotonic == Spec => LedgersMonoProp

=============================================================================