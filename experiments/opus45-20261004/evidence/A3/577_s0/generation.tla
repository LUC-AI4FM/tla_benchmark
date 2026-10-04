---- MODULE MCMultiNodeReadsAlt ----

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,
    Keys,
    Values,
    TransactionIds,
    MaxTransactions

VARIABLES
    ledgerBranches,
    history,
    nodeStates,
    pendingTransactions,
    committedTransactions

vars == <<ledgerBranches, history, nodeStates, pendingTransactions, committedTransactions>>

\* Type definitions for clarity
NullValue == CHOOSE v : v \notin Values

\* Transaction status constants
StatusPending == "pending"
StatusCommitted == "committed"
StatusAborted == "aborted"

\* Response type constants
ResponseSuccess == "success"
ResponseFailure == "failure"

\* Base specification actions (imported behavior)
\* Read action for a node reading a key
ReadKey(node, txId, key) ==
    /\ txId \in pendingTransactions
    /\ \E value \in Values \cup {NullValue}:
        /\ history' = Append(history, [
            type |-> "read",
            node |-> node,
            txId |-> txId,
            key |-> key,
            value |-> value,
            response |-> ResponseSuccess
           ])
        /\ UNCHANGED <<ledgerBranches, nodeStates, pendingTransactions, committedTransactions>>

\* Write action for a node writing a key-value pair
WriteKey(node, txId, key, value) ==
    /\ txId \in pendingTransactions
    /\ history' = Append(history, [
        type |-> "write",
        node |-> node,
        txId |-> txId,
        key |-> key,
        value |-> value,
        response |-> ResponseSuccess
       ])
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![node] = 
        [@ EXCEPT ![key] = value]]
    /\ UNCHANGED <<nodeStates, pendingTransactions, committedTransactions>>

\* Begin a new transaction
BeginTransaction(txId) ==
    /\ txId \notin pendingTransactions
    /\ txId \notin committedTransactions
    /\ Cardinality(pendingTransactions) + Cardinality(committedTransactions) < MaxTransactions
    /\ pendingTransactions' = pendingTransactions \cup {txId}
    /\ history' = Append(history, [
        type |-> "begin",
        txId |-> txId,
        response |-> ResponseSuccess
       ])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTransactions>>

\* Commit a transaction
CommitTransaction(txId) ==
    /\ txId \in pendingTransactions
    /\ pendingTransactions' = pendingTransactions \ {txId}
    /\ committedTransactions' = committedTransactions \cup {txId}
    /\ history' = Append(history, [
        type |-> "commit",
        txId |-> txId,
        response |-> ResponseSuccess,
        status |-> StatusCommitted
       ])
    /\ UNCHANGED <<ledgerBranches, nodeStates>>

\* Abort a transaction
AbortTransaction(txId) ==
    /\ txId \in pendingTransactions
    /\ pendingTransactions' = pendingTransactions \ {txId}
    /\ history' = Append(history, [
        type |-> "abort",
        txId |-> txId,
        response |-> ResponseSuccess,
        status |-> StatusAborted
       ])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTransactions>>

\* The imported next action from base specification
MCNextMultiNodeReadsAction ==
    \/ \E node \in Nodes, txId \in TransactionIds, key \in Keys:
        ReadKey(node, txId, key)
    \/ \E node \in Nodes, txId \in TransactionIds, key \in Keys, value \in Values:
        WriteKey(node, txId, key, value)
    \/ \E txId \in TransactionIds:
        BeginTransaction(txId)
    \/ \E txId \in TransactionIds:
        CommitTransaction(txId)
    \/ \E txId \in TransactionIds:
        AbortTransaction(txId)

\* Alternative initial state with two transactions already committed
\* This pre-populates the history with committed transactions
AltInit ==
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> NullValue]]
    \* Two transactions (tx1 and tx2) are already committed
    /\ \E tx1, tx2 \in TransactionIds:
        /\ tx1 # tx2
        /\ committedTransactions = {tx1, tx2}
        /\ pendingTransactions = {}
        \* History shows both transactions were begun and committed
        /\ history = <<
            [type |-> "begin", txId |-> tx1, response |-> ResponseSuccess],
            [type |-> "commit", txId |-> tx1, response |-> ResponseSuccess, status |-> StatusCommitted],
            [type |-> "begin", txId |-> tx2, response |-> ResponseSuccess],
            [type |-> "commit", txId |-> tx2, response |-> ResponseSuccess, status |-> StatusCommitted]
           >>
    /\ nodeStates = [n \in Nodes |-> "ready"]

\* Standard initial state for reference
Init ==
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> NullValue]]
    /\ history = <<>>
    /\ nodeStates = [n \in Nodes |-> "ready"]
    /\ pendingTransactions = {}
    /\ committedTransactions = {}

\* Next state relation
Next == MCNextMultiNodeReadsAction

\* Temporal specification starting from alternative initial state
\* Uses standard stuttering form
Spec == AltInit /\ [][MCNextMultiNodeReadsAction]_vars

\* Standard specification for comparison
StandardSpec == Init /\ [][MCNextMultiNodeReadsAction]_vars

\* Safety Invariants

\* Type invariant
TypeOK ==
    /\ ledgerBranches \in [Nodes -> [Keys -> Values \cup {NullValue}]]
    /\ history \in Seq([type: {"read", "write", "begin", "commit", "abort"},
                        txId: TransactionIds] \cup 
                       [type: {"read", "write"},
                        node: Nodes,
                        txId: TransactionIds,
                        key: Keys,
                        value: Values \cup {NullValue},
                        response: {ResponseSuccess, ResponseFailure}])
    /\ nodeStates \in [Nodes -> {"ready", "busy", "failed"}]
    /\ pendingTransactions \subseteq TransactionIds
    /\ committedTransactions \subseteq TransactionIds

\* No transaction can be both pending and committed
NoPendingAndCommitted ==
    pendingTransactions \cap committedTransactions = {}

\* Committed transactions count is bounded
BoundedCommitted ==
    Cardinality(committedTransactions) <= MaxTransactions

\* History is monotonically growing (safety)
HistoryMonotonic ==
    [][Len(history') >= Len(history)]_vars

\* Combined safety invariant
SafetyInvariant ==
    /\ NoPendingAndCommitted
    /\ BoundedCommitted

\* Liveness Properties

\* Every pending transaction eventually completes (commits or aborts)
\* Requires fairness on commit/abort actions
EventualCompletion ==
    \A txId \in TransactionIds:
        (txId \in pendingTransactions) ~> (txId \notin pendingTransactions)

\* The system can always make progress if there are pending transactions
Progress ==
    (pendingTransactions # {}) ~> (committedTransactions' # committedTransactions)

\* Fairness conditions
Fairness ==
    /\ WF_vars(MCNextMultiNodeReadsAction)

\* Full specification with fairness
FairSpec == Spec /\ Fairness

====