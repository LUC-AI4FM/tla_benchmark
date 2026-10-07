------------------------------- MODULE MCSpecMultiNodeReadsAlt -------------------------------
EXTENDS MCMultiNodeReads

CONSTANTS HistoryLimit, ViewLimit

VARIABLES ledger, history, requests, responses, committed, invalidated, sequenceNumbers, transactionIDs

InitAlt == 
  /\ ledger = [1 |-> <<>>, 2 |-> <<>>]
  /\ history = [1 |-> <<>>, 2 |-> <<>>]
  /\ requests = {}
  /\ responses = {}
  /\ committed = {1, 2}
  /\ invalidated = {}
  /\ sequenceNumbers = [t \in transactionIDs |-> CHOOSE sn \in Nat : sn NOT IN (DOMAIN sequenceNumbers)]
  /\ transactionIDs = {1, 2}

Init == InitAlt

Next == MCNextMultiNodeReadsAction

Spec ==
  /\ Init
  /\ [][Next]_<<ledger, history, requests, responses, committed, invalidated, sequenceNumbers, transactionIDs>>
  /\ WF_[Next]_<<ledger, history, requests, responses, committed, invalidated, sequenceNumbers, transactionIDs>>

\* Safety invariants inherited from MCMultiNodeReads
SafetyInvariant1 == \A t \in committed: \A sn \in sequenceNumbers[t]: \A v \in DOMAIN ledger: \E e \in ledger[v]: e = <<t, sn>>
SafetyInvariant2 == \A t1, t2 \in transactionIDs: t1 # t2 => sequenceNumbers[t1] # sequenceNumbers[t2]
SafetyInvariant3 == \A t \in committed: \A v \in DOMAIN ledger: \E e \in ledger[v]: e = <<t, sequenceNumbers[t]>>
SafetyInvariant4 == \A t \in invalidated: \A v \in DOMAIN ledger: \A e \in ledger[v]: e # <<t, sequenceNumbers[t]>>

\* Additional safety invariants can be added here as needed

=============================================================================