---- MODULE AltInitMultiNodeReads ----
EXTENDS Sequences

CONSTANTS
  NODES,
  TXNS,
  Txn1,
  Txn2

VARIABLES
  ledger,
  history

vars == << ledger, history >>

Types == {"Response", "CommittedStatus"}

TypeOK ==
  /\ ledger \in [NODES -> Seq(TXNS)]
  /\ history \in Seq([type: Types, txn: TXNS])

DistinctTxns ==
  /\ Txn1 \in TXNS
  /\ Txn2 \in TXNS
  /\ Txn1 # Txn2

CommittedPair ==
  << [type |-> "Response",        txn |-> Txn1],
     [type |-> "CommittedStatus", txn |-> Txn1],
     [type |-> "Response",        txn |-> Txn2],
     [type |-> "CommittedStatus", txn |-> Txn2] >>

Init ==
  /\ DistinctTxns
  /\ ledger = [ n \in NODES |-> << Txn1, Txn2 >> ]
  /\ history = CommittedPair
  /\ TypeOK

MCNextMultiNodeReadsAction ==
  \/ \E n \in NODES, t \in TXNS:
       /\ ledger' = [ledger EXCEPT ![n] = Append(@, t)]
       /\ history' = history
  \/ \E t \in TXNS:
       /\ ledger' = ledger
       /\ history' = Append(history, [type |-> "Response", txn |-> t])
  \/ \E t \in TXNS:
       /\ ledger' = ledger
       /\ history' = Append(history, [type |-> "CommittedStatus", txn |-> t])

Next == MCNextMultiNodeReadsAction

Spec ==
  Init /\ [][MCNextMultiNodeReadsAction]_vars

Invariant == TypeOK

====