------------------------- MODULE MCSingleNodeReads -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Key,            \* set of keys
    Value,          \* set of values that may be written
    Txn,            \* set of read-only transaction identifiers
    MaxLogLen,      \* bound on the number of writes on the single node
    MaxHistoryLen   \* bound on the length of the read-only txn history

ASSUME MaxLogLen \in Nat /\ MaxHistoryLen \in Nat

NoValue == CHOOSE v : v \notin Value

VARIABLES
    log,            \* sequence of writes [key, value] on the single node
    commitIndex,    \* index of the last committed write
    txnState,       \* per-transaction state for read-only transactions
    history         \* history of read-only txn request/response events

vars == <<log, commitIndex, txnState, history>>

-----------------------------------------------------------------------------
(* Helpers *)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Value of key k as of snapshot timestamp ts (log index).
ReadAt(k, ts) ==
    LET idxs == {i \in 1..ts : log[i].key = k}
    IN IF idxs = {} THEN NoValue ELSE log[Max(idxs)].value

Event ==
    [type : {"req"}, txn : Txn, readTs : Nat]
    \cup
    [type : {"resp"}, txn : Txn, readTs : Nat, key : Key, value : Value \cup {NoValue}]

-----------------------------------------------------------------------------
(* Single-node read system *)

Init ==
    /\ log = <<>>
    /\ commitIndex = 0
    /\ txnState = [t \in Txn |-> [active |-> FALSE, readTs |-> 0]]
    /\ history = <<>>

\* A write on the single node; it commits immediately.
ClientWrite(k, v) ==
    /\ Len(log) < MaxLogLen
    /\ log' = Append(log, [key |-> k, value |-> v])
    /\ commitIndex' = Len(log) + 1
    /\ UNCHANGED <<txnState, history>>

\* Start a read-only transaction at the current committed snapshot.
ROTxnRequest(t) ==
    /\ ~txnState[t].active
    /\ txnState' = [txnState EXCEPT ![t] = [active |-> TRUE, readTs |-> commitIndex]]
    /\ history' = Append(history, [type |-> "req", txn |-> t, readTs |-> commitIndex])
    /\ UNCHANGED <<log, commitIndex>>

\* Respond to a read-only transaction by reading a key at its snapshot.
ROTxnResponse(t) ==
    /\ txnState[t].active
    /\ \E k \in Key :
        history' = Append(history,
                          [type   |-> "resp",
                           txn    |-> t,
                           readTs |-> txnState[t].readTs,
                           key    |-> k,
                           value  |-> ReadAt(k, txnState[t].readTs)])
    /\ txnState' = [txnState EXCEPT ![t].active = FALSE]
    /\ UNCHANGED <<log, commitIndex>>

\* Existing single-node next-state action (non read-only-txn steps).
NextSingleNodeAction ==
    \E k \in Key, v \in Value : ClientWrite(k, v)

-----------------------------------------------------------------------------
(* Bounded model-checking wrapper *)

MCROTxnRequest(t) ==
    /\ Len(history) < MaxHistoryLen
    /\ ROTxnRequest(t)

MCROTxnResponse(t) ==
    /\ Len(history) < MaxHistoryLen
    /\ ROTxnResponse(t)

MCNextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ \E t \in Txn : MCROTxnRequest(t)
    \/ \E t \in Txn : MCROTxnResponse(t)

Spec == Init /\ [][MCNextSingleNodeReadsAction]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ log \in Seq([key : Key, value : Value])
    /\ Len(log) <= MaxLogLen
    /\ commitIndex \in 0..Len(log)
    /\ txnState \in [Txn -> [active : BOOLEAN, readTs : Nat]]
    /\ history \in Seq(Event)
    /\ Len(history) <= MaxHistoryLen

\* Every snapshot timestamp refers to a committed point in the log.
SnapshotCommitted ==
    \A t \in Txn : txnState[t].readTs <= commitIndex

\* Every read response returns the value as of the transaction's snapshot.
ReadsAreSnapshotConsistent ==
    \A i \in 1..Len(history) :
        history[i].type = "resp" =>
            /\ history[i].readTs <= commitIndex
            /\ history[i].value = ReadAt(history[i].key, history[i].readTs)

\* Every response is preceded by a matching request from the same transaction.
ResponsesHaveRequests ==
    \A i \in 1..Len(history) :
        history[i].type = "resp" =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = "req"
                /\ history[j].txn = history[i].txn
                /\ history[j].readTs = history[i].readTs

=============================================================================