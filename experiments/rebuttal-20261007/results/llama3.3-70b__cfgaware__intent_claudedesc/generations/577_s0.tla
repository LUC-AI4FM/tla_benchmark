------------------------------- MODULE MCSpecMultiNodeReadsAlt -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
  NumNodes,
  MaxView,
  MaxSequence,
  InitialTransactions,
  InitialBranches

VARIABLES
  ledger,
  clientRequests,
  transactionStatus,
  currentView,
  sequenceNumber,
  branchMap

TypeInvariant ==
  /\ ledger \in [1..NumNodes -> SUBSET Seq(Transaction)]
  /\ clientRequests \in [Client -> Seq(TransactionRequest)]
  /\ transactionStatus \in [TransactionID -> {Committed, Pending}]
  /\ currentView \in 1..MaxView
  /\ sequenceNumber \in 1..MaxSequence
  /\ branchMap \in [1..NumNodes -> Branch]

Transaction == [view: 1..MaxView, sequence: 1..MaxSequence, data: Data]
TransactionID == [view: 1..MaxView, sequence: 1..MaxSequence]
TransactionRequest == [transaction: Transaction, observed: SUBSET TransactionID]
Data == String

Branch == Seq(Transaction)

Init ==
  /\ ledger = [n \in 1..NumNodes |-> {}]
  /\ clientRequests = [c \in Client |-> <<>>]
  /\ transactionStatus = []
  /\ currentView = 1
  /\ sequenceNumber = 1
  /\ branchMap = [n \in 1..NumNodes |-> <<>>]

InitAlt ==
  /\ ledger = InitialBranches
  /\ clientRequests = [c \in Client |-> <<>>]
  /\ transactionStatus = [t \in InitialTransactions |-> Committed]
  /\ currentView = MaxView
  /\ sequenceNumber = MaxSequence
  /\ branchMap = [n \in 1..NumNodes |-> <<>>]

Next ==
  \/ \E c \in Client, t \in Transaction :
      /\ clientRequests' = [clientRequests EXCEPT ![c] = Append(clientRequests[c], <<t>>)]
      /\ transactionStatus' = transactionStatus
      /\ ledger' = ledger
      /\ currentView' = currentView
      /\ sequenceNumber' = sequenceNumber
      /\ branchMap' = branchMap
  \/ \E n \in 1..NumNodes, t \in Transaction :
      /\ ledger' = [ledger EXCEPT ![n] = Append(ledger[n], t)]
      /\ clientRequests' = clientRequests
      /\ transactionStatus' = [transactionStatus EXCEPT ![t.view, t.sequence] = Committed]
      /\ currentView' = currentView
      /\ sequenceNumber' = sequenceNumber
      /\ branchMap' = branchMap
  \/ \E n \in 1..NumNodes :
      /\ ledger' = [ledger EXCEPT ![n] = <<>>]
      /\ clientRequests' = clientRequests
      /\ transactionStatus' = []
      /\ currentView' = currentView + 1
      /\ sequenceNumber' = 1
      /\ branchMap' = [branchMap EXCEPT ![n] = <<>>]

ReadConsistency ==
  \A t1, t2 \in Transaction :
    (t1.view < t2.view) => (t2.observed \subseteq t1.observed)

Linearizability ==
  \A t1, t2 \in Transaction :
    (t1.view < t2.view) => ((t2.observed \cap {t1}) = {})

BranchConsistency ==
  \A n1, n2 \in 1..NumNodes :
    /\ ledger[n1] \subseteq ledger[n2]
    => branchMap[n1] \subseteq branchMap[n2]

Spec == InitAlt /\ [][Next]_<<ledger, clientRequests, transactionStatus, currentView, sequenceNumber, branchMap>>
THEOREM Spec => []ReadConsistency
THEOREM Spec => []Linearizability
THEOREM Spec => []BranchConsistency

=============================================================================