```
MODULE MCMultiNodeReadsAlt
EXTENDS MCMultiNodeReads
CONSTANTS HistoryLimit, ViewLimit
VARIABLES ledger, history, requests, responses, transactions

InitAlt == 
  /\ ledger = [view1 |-> <<>, view2 |-> <>]
  /\ history = <<RequestTxn(1), ResponseTxn(1, Committed), RequestTxn(2), ResponseTxn(2, Committed)>>
  /\ requests = {}
  /\ responses = {}
  /\ transactions = {}

MCNextMultiNodeReadsAction == 
  MCNextMultiNodeReadsAction

MCSpecMultiNodeReadsAlt == 
  /\ InitAlt
  /\ [][MCNextMultiNodeReadsAction]_<<ledger, history, requests, responses, transactions>>
  /\ WF_<<ledger, history, requests, responses, transactions>>(MCNextMultiNodeReadsAction)
  /\ HistoryLimit = 11
  /\ ViewLimit = 3

Spec == MCSpecMultiNodeReadsAlt

THEOREM Spec => 
  /\ InvSerializableReads
  /\ InvUniqueTxnIds
  /\ InvUniqueSeqNos
  /\ InvConsistentObservations
  /\ InvInvalidatedTxsNeverObserved
  /\ InvNoDeadlocksDisabled
  /\ InvLedgerBranches
  /\ InvHistoryRecords
  /\ InvRequestResponsePairs
  /\ InvCommittedStatusReceipts
  /\ InvTransactionUniqueness
  /\ InvViewAndSeqNoConsistency

InvSerializableReads == 
  \A t1, t2 \in Domain(transactions) : 
    (t1 # t2) => (SerializableRead(t1, t2) \/ SerializableRead(t2, t1))

InvUniqueTxnIds == 
  \A t1, t2 \in Domain(transactions) : 
    t1 # t2 => transactions[t1].id # transactions[t2].id

InvUniqueSeqNos == 
  \A t1, t2 \in Domain(transactions) : 
    t1 # t2 => transactions[t1].seqNo # transactions[t2].seqNo

InvConsistentObservations == 
  \A r \in requests, t \in responses : 
    (r.id = t.id) => (requests[r].observed = responses[t].observed)

InvInvalidatedTxsNeverObserved == 
  \A t1, t2 \in Domain(transactions) : 
    (t1 # t2) /\ transactions[t1].invalidated => ~(SerializableRead(t1, t2))

InvNoDeadlocksDisabled == TRUE

InvLedgerBranches == 
  \A b \in Domain(ledger) : 
    ledger[b] # <<>>

InvHistoryRecords == 
  \A h \in history : 
    (h.type = "Request") \/ (h.type = "Response")

InvRequestResponsePairs == 
  \A r \in requests, t \in responses : 
    (r.id = t.id) => (requests[r].type = "Request") /\ (responses[t].type = "Response")

InvCommittedStatusReceipts == 
  \A t \in responses : 
    (t.type = "Response") => (t.status = Committed)

InvTransactionUniqueness == 
  \A t1, t2 \in Domain(transactions) : 
    t1 # t2 => transactions[t1] # transactions[t2]

InvViewAndSeqNoConsistency == 
  \A t \in Domain(transactions) : 
    (transactions[t].view <= ViewLimit) /\ (transactions[t].seqNo <= HistoryLimit)
```