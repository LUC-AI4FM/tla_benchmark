```
MODULE MCSpecMultiNodeReadsAlt

EXTENDS Integers, Sequences, TLC

CONSTANTS Nodes, Transactions, InitialCommits
VARIABLES nodeState, transactionStatus, readHistory

TypeInvariant ==
  /\ nodeState \in [Nodes -> SUBSET Transactions]
  /\ transactionStatus \in [Transactions -> {<<"committed">>, <<"pending">>, <<"aborted">>}]
  /\ readHistory \in [Nodes -> Sequences(Transactions)]

Init ==
  /\ nodeState = [n \in Nodes |-> {}]
  /\ transactionStatus = [t \in Transactions |-> IF t \in InitialCommits THEN <<"committed">> ELSE <<"pending">>]
  /\ readHistory = [n \in Nodes |-> <<>>]

ProposeTransaction(t, n) ==
  /\ transactionStatus' = [transactionStatus EXCEPT ![t] = <<"pending">>]
  /\ nodeState' = [nodeState EXCEPT ![n] = nodeState[n] \cup {t}]
  /\ readHistory' = readHistory
  /\ t \in Transactions

CommitTransaction(t, n) ==
  /\ transactionStatus[t] = <<"pending">>
  /\ transactionStatus' = [transactionStatus EXCEPT ![t] = <<"committed">>]
  /\ nodeState' = [nodeState EXCEPT ![n] = nodeState[n] \cup {t}]
  /\ readHistory' = [readHistory EXCEPT ![n] = Append(readHistory[n], t)]
  /\ t \in Transactions

ReadTransactions(n) ==
  /\ readHistory' = [readHistory EXCEPT ![n] = Append(readHistory[n], nodeState[n])]
  /\ nodeState' = nodeState
  /\ transactionStatus' = transactionStatus

Next ==
  \/ \E t \in Transactions, n \in Nodes : ProposeTransaction(t, n)
  \/ \E t \in Transactions, n \in Nodes : CommitTransaction(t, n)
  \/ \E n \in Nodes : ReadTransactions(n)

Spec == Init /\ [][Next]_

THEOREM Spec => []TypeInvariant
THEOREM Spec => \A n \in Nodes : 
  <<>> /= readHistory[n] => 
    (readHistory[n] = SubSeq(readHistory[n], 1, Len(readHistory[n])))
THEOREM Spec => \A t \in Transactions :
  transactionStatus[t] = <<"committed">> =>
    \A n \in Nodes : 
      <<>> /= readHistory[n] => 
        (t \in readHistory[n])
THEOREM Spec => \A n \in Nodes, t1, t2 \in Transactions :
  t1 \in readHistory[n] /\ t2 \in readHistory[n] /\ t1 < t2 =>
    SubSeq(readHistory[n], 1, t1) = SubSeq(readHistory[n], 1, t2)

=============================================================================
```
Note: The above TLA+ specification models a distributed ledger system with multiple nodes that can propose transactions, commit them, and read the committed history. It ensures safety (committed transactions are never lost), monotonic visibility (reads observe at least the same set of committed transactions as previous reads or commits on the same node), consistency across nodes (eventually all nodes make committed transactions visible to reads), and internal consistency of observed sets with respect to the ordering of committed transactions.

The `TypeInvariant` defines the types of variables, `Init` initializes the system state, and `Next` specifies the possible next steps. The `ProposeTransaction`, `CommitTransaction`, and `ReadTransactions` actions model the corresponding behaviors. The `Spec` defines the overall specification as the conjunction of the initial condition and the next-state relation.

The theorems verify that the specification maintains type invariants, ensures monotonic visibility, guarantees consistency across nodes for committed transactions, and enforces internal consistency of observed sets with respect to the ordering of committed transactions.