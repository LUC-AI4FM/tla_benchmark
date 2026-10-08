```tla
MODULE DistributedLedger

EXTENDS Integers, Sequences, TLC

CONSTANTS
  NumNodes,
  MaxView,
  MaxSequence,
  InitialTransactions

VARIABLES
  ledger,
  clientRequests,
  transactionStatus,
  currentView,
  sequenceNumber,
  branchMap

Init ==
  /\ ledger = [i \in 1..NumNodes |-> <<>>]
  /\ clientRequests = {}
  /\ transactionStatus = {}
  /\ currentView = 1
  /\ sequenceNumber = 1
  /\ branchMap = {}

AlternativeInit ==
  /\ ledger = [i \in 1..NumNodes |-> InitialTransactions]
  /\ clientRequests = {<<1, 1>> :> "committed"}
  /\ transactionStatus = {<<1, 1>> :> "committed"}
  /\ currentView = MaxView
  /\ sequenceNumber = MaxSequence
  /\ branchMap = [i \in 1..NumNodes |-> <<>>]

SubmitTransaction(client, view, sequence) ==
  /\ clientRequests' = clientRequests \cup {<<view, sequence>> :> "pending"}
  /\ transactionStatus' = [transactionStatus EXCEPT ![<<view, sequence>>] = "pending"]
  /\ ledger' = [ledger EXCEPT !currentView = Append(ledger[currentView], <<view, sequence>>)]
  /\ currentView' = view
  /\ sequenceNumber' = sequence + 1
  /\ UNCHANGED branchMap

RespondToTransaction(client, view, sequence) ==
  /\ clientRequests' = clientRequests \ {<<view, sequence>>}
  /\ transactionStatus' = [transactionStatus EXCEPT ![<<view, sequence>>] = "committed"]
  /\ ledger' = [ledger EXCEPT !currentView = Append(ledger[currentView], <<view, sequence>>)]
  /\ currentView' = view
  /\ sequenceNumber' = sequence + 1
  /\ branchMap' = [branchMap EXCEPT ![currentView] = Append(branchMap[currentView], <<view, sequence>>)]
  /\ UNCHANGED clientRequests

Next ==
  \/ \E client \in 1..NumNodes : 
    \E view \in 1..MaxView :
    \E sequence \in 1..MaxSequence :
      SubmitTransaction(client, view, sequence)
  \/ \E client \in 1..NumNodes : 
    \E view \in 1..MaxView :
    \E sequence \in 1..MaxSequence :
      RespondToTransaction(client, view, sequence)

Spec ==
  /\ (Init /\ [][Next]_)
  /\ WF_vars(SubmitTransaction)
  /\ SF_vars(RespondToTransaction)

ReadConsistency ==
  \A client \in 1..NumNodes :
  \A view \in 1..MaxView :
  \A sequence \in 1..MaxSequence :
    (transactionStatus[<<view, sequence>>] = "committed") =>
      (\A priorView \in 1..view :
        \A priorSequence \in 1..sequence :
          (priorView < view \/ (priorView = view /\ priorSequence <= sequence)) =>
            (transactionStatus[<<priorView, priorSequence>>] = "committed"))

Linearizability ==
  \A client \in 1..NumNodes :
  \A view \in 1..MaxView :
  \A sequence \in 1..MaxSequence :
    (transactionStatus[<<view, sequence>>] = "committed") =>
      (\E priorView \in 1..view :
        \E priorSequence \in 1..sequence :
          (priorView < view \/ (priorView = view /\ priorSequence <= sequence)) =>
            (transactionStatus[<<priorView, priorSequence>>] = "committed"))

BranchConsistency ==
  \A client \in 1..NumNodes :
  \A view \in 1..MaxView :
  \A sequence \in 1..MaxSequence :
    (branchMap[currentView] = <<view, sequence>>) =>
      (\A priorView \in 1..view :
        \A priorSequence \in 1..sequence :
          (priorView < view \/ (priorView = view /\ priorSequence <= sequence)) =>
            (branchMap[priorView] = <<priorView, priorSequence>>))

THEOREM Spec => []ReadConsistency
THEOREM Spec => []Linearizability
THEOREM Spec => []BranchConsistency

```
Note: The above TLA+ specification models the distributed ledger system with read consistency, linearizability, and branch consistency properties. It includes an alternative initial state configuration that starts the system with some transactions already committed.