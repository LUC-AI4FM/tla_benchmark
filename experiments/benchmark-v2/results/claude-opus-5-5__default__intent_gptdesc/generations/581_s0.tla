------------------------------- MODULE SingleNodeTxService -------------------------------
(***************************************************************************)
(* Abstract model of a single-node transaction processing service.        *)
(*                                                                         *)
(* Clients issue read-write transaction requests. The node executes them,  *)
(* one at a time and atomically, against a sequential abstract datastore.  *)
(* The datastore is modelled as a ledger: the sequence of executed         *)
(* transactions in serial order. Each read-write transaction reads the     *)
(* entire current state and appends its own identifier. Its position in    *)
(* the ledger is its transaction id (tid).                                 *)
(*                                                                         *)
(* Responses report what the transaction observed and the tid it received. *)
(* After the ledger prefix containing a transaction becomes durable        *)
(* (committed), the node may emit a committed-status event for that tid.   *)
(*                                                                         *)
(* All observable events are recorded in a history whose length is        *)
(* bounded by HistoryLimit, so the model can be checked exhaustively.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT HistoryLimit

ASSUME HistoryLimitAssumption == HistoryLimit \in Nat \ {0}

VARIABLES
    history,      \* sequence of observable events
    ledger,       \* serial order of executed transactions (abstract datastore)
    commitIndex   \* length of the durably applied (committed) ledger prefix

vars == <<history, ledger, commitIndex>>

-----------------------------------------------------------------------------
(* Identifiers and event shapes *)

\* Every request consumes one history slot, so there are never more than
\* HistoryLimit transactions.
TxIds  == 1 .. HistoryLimit
TxTids == 1 .. HistoryLimit

RequestEvents ==
    [type : {"RwTxRequest"}, tx : TxIds]

ResponseEvents ==
    [type : {"RwTxResponse"}, tx : TxIds, observed : Seq(TxIds), tid : TxTids]

StatusEvents ==
    [type : {"TxStatusReceived"}, tid : TxTids, status : {"CommittedStatus"}]

Events == RequestEvents \cup ResponseEvents \cup StatusEvents

-----------------------------------------------------------------------------
(* Helper operators over the history and the ledger *)

HistoryFull == Len(history) >= HistoryLimit

RequestIdx  == {i \in DOMAIN history : history[i].type = "RwTxRequest"}
ResponseIdx == {i \in DOMAIN history : history[i].type = "RwTxResponse"}
StatusIdx   == {i \in DOMAIN history : history[i].type = "TxStatusReceived"}

Requested(t) == \E i \in RequestIdx  : history[i].tx = t
Responded(t) == \E i \in ResponseIdx : history[i].tx = t
RespondedTid(j) == \E i \in ResponseIdx : history[i].tid = j
StatusEmitted(j) == \E i \in StatusIdx : history[i].tid = j

Executed(t) == \E j \in DOMAIN ledger : ledger[j] = t
Committed(j) == j \in 1 .. commitIndex

RequestedTxs == {history[i].tx : i \in RequestIdx}

Range(s) == {s[k] : k \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ history = <<>>
    /\ ledger = <<>>
    /\ commitIndex = 0

-----------------------------------------------------------------------------
(* Actions *)

\* A client issues a new read-write transaction request.
RwTxRequest ==
    /\ ~HistoryFull
    /\ history' = Append(history,
                    [type |-> "RwTxRequest",
                     tx   |-> Cardinality(RequestIdx) + 1])
    /\ UNCHANGED <<ledger, commitIndex>>

\* The node executes a pending request atomically: it reads the full
\* current state and appends itself to the serial order. Requests may be
\* executed in any order relative to their arrival.
RwTxExecute ==
    \E t \in RequestedTxs :
        /\ ~Executed(t)
        /\ ledger' = Append(ledger, t)
        /\ UNCHANGED <<history, commitIndex>>

\* The node responds to an executed transaction, reporting the state it
\* observed (everything serially before it) and its tid. Responses may be
\* emitted in any order, but only after the matching execution.
RwTxResponse ==
    /\ ~HistoryFull
    /\ \E j \in DOMAIN ledger :
        /\ ~Responded(ledger[j])
        /\ history' = Append(history,
                        [type     |-> "RwTxResponse",
                         tx       |-> ledger[j],
                         observed |-> SubSeq(ledger, 1, j - 1),
                         tid      |-> j])
    /\ UNCHANGED <<ledger, commitIndex>>

\* A longer prefix of the ledger becomes durably applied.
CommitTx ==
    /\ commitIndex < Len(ledger)
    /\ \E k \in (commitIndex + 1) .. Len(ledger) : commitIndex' = k
    /\ UNCHANGED <<history, ledger>>

\* The node reports the committed status of a transaction that was
\* executed, has been responded to, and is now durable.
StatusCommittedResponse ==
    /\ ~HistoryFull
    /\ \E j \in 1 .. commitIndex :
        /\ RespondedTid(j)
        /\ ~StatusEmitted(j)
        /\ history' = Append(history,
                        [type   |-> "TxStatusReceived",
                         tid    |-> j,
                         status |-> "CommittedStatus"])
    /\ UNCHANGED <<ledger, commitIndex>>

\* Terminal stuttering once the bounded run is exhausted and all
\* internal work is complete (avoids spurious deadlock reports).
Done ==
    /\ HistoryFull
    /\ \A t \in RequestedTxs : Executed(t)
    /\ commitIndex = Len(ledger)
    /\ UNCHANGED vars

Next ==
    \/ RwTxRequest
    \/ RwTxExecute
    \/ RwTxResponse
    \/ CommitTx
    \/ StatusCommittedResponse
    \/ Done

Fairness ==
    /\ WF_vars(RwTxExecute)
    /\ WF_vars(RwTxResponse)
    /\ WF_vars(CommitTx)
    /\ WF_vars(StatusCommittedResponse)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: well-formedness and consistency *)

TypeOK ==
    /\ history \in Seq(Events)
    /\ ledger \in Seq(TxIds)
    /\ commitIndex \in 0 .. Len(ledger)

\* The observable history never exceeds its bound.
HistoryBoundInv == Len(history) <= HistoryLimit

\* Requests carry fresh, consecutive identifiers.
RequestIdsWellFormedInv ==
    /\ \A i, k \in RequestIdx : i # k => history[i].tx # history[k].tx
    /\ RequestedTxs = 1 .. Cardinality(RequestIdx)

\* No dangling references in the state: every executed transaction was
\* requested, and each was executed at most once (atomicity).
LedgerConsistentInv ==
    /\ Range(ledger) \subseteq RequestedTxs
    /\ \A j, k \in DOMAIN ledger : j # k => ledger[j] # ledger[k]

\* Every response matches an earlier request, and each request receives at
\* most one response.
ResponseMatchesRequestInv ==
    /\ \A i \in ResponseIdx :
        \E r \in RequestIdx : r < i /\ history[r].tx = history[i].tx
    /\ \A i, k \in ResponseIdx :
        i # k => history[i].tx # history[k].tx

\* Each response reflects a legal result of serial execution on the
\* abstract datastore: the transaction sits at position tid and observed
\* exactly the state produced by all serially earlier transactions.
ResponseLegalResultInv ==
    \A i \in ResponseIdx :
        LET e == history[i] IN
        /\ e.tid \in DOMAIN ledger
        /\ ledger[e.tid] = e.tx
        /\ e.observed = SubSeq(ledger, 1, e.tid - 1)

\* Isolation / serializability judged purely from the observable history:
\* responses are mutually consistent with one single serial order.
SerializableHistoryInv ==
    \A i, k \in ResponseIdx :
        LET a == history[i]
            b == history[k]
        IN
        /\ Len(a.observed) = a.tid - 1
        /\ (a.tid = b.tid) => (a.tx = b.tx)
        /\ (a.tid < b.tid) =>
              /\ IsPrefix(a.observed, b.observed)
              /\ b.observed[a.tid] = a.tx
        /\ a.tx \notin Range(a.observed)

\* Committed-status events only concern transactions that were executed,
\* responded to beforehand, and are durably applied; at most one per tid.
CommittedStatusInv ==
    /\ \A i \in StatusIdx :
        /\ history[i].tid \in DOMAIN ledger
        /\ Committed(history[i].tid)
        /\ \E r \in ResponseIdx : r < i /\ history[r].tid = history[i].tid
    /\ \A i, k \in StatusIdx : i # k => history[i].tid # history[k].tid

\* Durability: the committed prefix of the datastore never changes.
CommittedPrefixStable ==
    [][ /\ commitIndex' >= commitIndex
        /\ SubSeq(ledger', 1, commitIndex) = SubSeq(ledger, 1, commitIndex)
        /\ IsPrefix(ledger, ledger')
        /\ IsPrefix(history, history') ]_vars

ConsistencyInv ==
    /\ TypeOK
    /\ HistoryBoundInv
    /\ RequestIdsWellFormedInv
    /\ LedgerConsistentInv
    /\ ResponseMatchesRequestInv
    /\ ResponseLegalResultInv
    /\ SerializableHistoryInv
    /\ CommittedStatusInv

-----------------------------------------------------------------------------
(* Liveness: bounded progress *)

\* Every requested transaction is eventually executed.
EventuallyExecuted ==
    \A t \in TxIds : Requested(t) ~> Executed(t)

\* Every requested transaction eventually receives a response, unless the
\* bounded history prevents it.
EventuallyResponded ==
    \A t \in TxIds : Requested(t) ~> (Responded(t) \/ HistoryFull)

\* Every executed transaction eventually becomes durable.
EventuallyCommitted ==
    \A j \in TxTids : (j \in DOMAIN ledger) ~> Committed(j)

\* Committed-status notifications eventually appear for responded,
\* committed transactions, unless the bounded history prevents it.
EventuallyCommittedStatus ==
    \A j \in TxTids : RespondedTid(j) ~> (StatusEmitted(j) \/ HistoryFull)

Liveness ==
    /\ EventuallyExecuted
    /\ EventuallyResponded
    /\ EventuallyCommitted
    /\ EventuallyCommittedStatus

THEOREM Spec => []ConsistencyInv /\ CommittedPrefixStable /\ Liveness

=============================================================================