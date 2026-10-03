----------------------------- MODULE AltInitMultiNodeReads -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Nodes, \* Non-empty set of nodes
    Txns,  \* Set of transaction identifiers
    TxA,   \* A specific transaction in Txns
    TxB    \* Another specific transaction in Txns, distinct from TxA

ASSUME
    /\ Nodes # {}
    /\ TxA \in Txns
    /\ TxB \in Txns
    /\ TxA # TxB

VARIABLES
    ledger,   \* Per-node ledger branches: each node maps to a sequence of committed transactions
    history   \* History of events (responses and committed-status records)

vars == << ledger, history >>

\* Helper: membership of an element in a sequence
InSeq(s, x) == \E i \in 1..Len(s): s[i] = x

\* Allowed history element shapes
HistoryElems ==
    { [type |-> "Resp",      txn |-> t, committed |-> FALSE] : t \in Txns } \cup
    { [type |-> "Committed", txn |-> t, committed |-> TRUE ] : t \in Txns }

\* Type correctness
TypeOK ==
    /\ ledger \in [Nodes -> Seq(Txns)]
    /\ history \in Seq(HistoryElems)

\* Pre-populated history reflecting that two transactions are already committed
AltHistory ==
    << [type |-> "Resp",      txn |-> TxA, committed |-> FALSE],
       [type |-> "Committed", txn |-> TxA, committed |-> TRUE ],
       [type |-> "Resp",      txn |-> TxB, committed |-> FALSE],
       [type |-> "Committed", txn |-> TxB, committed |-> TRUE ] >>

\* Alternative initial state: all nodes have both transactions in their ledger branches,
\* and history includes response and committed-status records for both.
AltInit ==
    /\ TypeOK
    /\ ledger = [ n \in Nodes |-> << TxA, TxB >> ]
    /\ history = AltHistory

Init == AltInit

\* Imported next-step action for the multi-node reads model.
\* Here provided as a placeholder; the temporal spec uses the standard stuttering form.
MCNextMultiNodeReadsAction == UNCHANGED vars

Next == MCNextMultiNodeReadsAction

\* Safety predicates (useful for model checking)
CommittedOnAllNodes(t) == \A n \in Nodes: InSeq(ledger[n], t)

HistoryShowsCommit(t) ==
    /\ InSeq(history, [type |-> "Resp",      txn |-> t, committed |-> FALSE])
    /\ InSeq(history, [type |-> "Committed", txn |-> t, committed |-> TRUE ])

SafetyInv ==
    /\ TypeOK
    /\ CommittedOnAllNodes(TxA)
    /\ CommittedOnAllNodes(TxB)
    /\ \A t \in {TxA, TxB}: HistoryShowsCommit(t)

\* Temporal specification: starts from the alternative initial state and evolves
\* according to MCNextMultiNodeReadsAction, using the standard stuttering form.
Spec == Init /\ [][MCNextMultiNodeReadsAction]_vars

========================================================================================