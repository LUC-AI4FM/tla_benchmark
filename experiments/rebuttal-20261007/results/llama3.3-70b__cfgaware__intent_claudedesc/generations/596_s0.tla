---------------------------- MODULE DistributedTransactionSystem ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Keys, Clients, PrimaryKeys
VARIABLES clientState, keyLocks, keyValues, transactionLog, messageTimestamps

TypeInvariant == 
  /\ clientState \in [Clients -> {[keysToRead : SUBSET Keys, keysToWrite : SUBSET Keys, primaryKey : Keys]}]
  /\ keyLocks \in [Keys -> Clients \cup {<<"none">>}]
  /\ keyValues \in [Keys -> Int]
  /\ transactionLog \in Sequence([Clients -> {[transactionStatus : {"committed", "aborted"}, readSnapshot : [Keys -> Int], writtenKeys : SUBSET Keys]}])
  /\ messageTimestamps \in [Sequences -> Int]

Init == 
  /\ clientState = [c \in Clients |-> [keysToRead |-> {}, keysToWrite |-> {}, primaryKey |-> PrimaryKeys[c]]]
  /\ keyLocks = [k \in Keys |-> <<"none">>]
  /\ keyValues = [k \in Keys |-> 0]
  /\ transactionLog = <<>>
  /\ messageTimestamps = [s \in Sequences |-> 0]

OptimisticRead(c, k) == 
  /\ clientState[c].keysToRead = {}
  /\ keyLocks[k] = <<"none">>
  /\ clientState' = [clientState EXCEPT ![c].keysToRead = {k}]
  /\ UNCHANGED <<keyLocks, keyValues, transactionLog, messageTimestamps>>

PessimisticLock(c, k) == 
  /\ keyLocks[k] = <<"none">>
  /\ keyLocks' = [keyLocks EXCEPT ![k] = c]
  /\ clientState' = [clientState EXCEPT ![c].keysToWrite = {k}]
  /\ UNCHANGED <<keyValues, transactionLog, messageTimestamps>>

CommitTransaction(c) == 
  /\ clientState[c].transactionStatus = "committed"
  /\ transactionLog' = Append(transactionLog, [c |-> [transactionStatus |-> "committed", readSnapshot |-> keyValues, writtenKeys |-> clientState[c].keysToWrite]])
  /\ keyLocks' = [k \in Keys |-> IF keyLocks[k] = c THEN <<"none">> ELSE keyLocks[k]]
  /\ keyValues' = [k \in Keys |-> IF k \in clientState[c].keysToWrite THEN clientState[c].readSnapshot[k] + 1 ELSE keyValues[k]]
  /\ messageTimestamps' = [s \in Sequences |-> messageTimestamps[s] + 1]
  /\ UNCHANGED <<clientState>>

AbortTransaction(c) == 
  /\ clientState[c].transactionStatus = "aborted"
  /\ transactionLog' = Append(transactionLog, [c |-> [transactionStatus |-> "aborted", readSnapshot |-> {}, writtenKeys |-> {}]])
  /\ keyLocks' = [k \in Keys |-> IF keyLocks[k] = c THEN <<"none">> ELSE keyLocks[k]]
  /\ UNCHANGED <<keyValues, messageTimestamps, clientState>>

Next == 
  \/ \E c \in Clients : \E k \in Keys : OptimisticRead(c, k)
  \/ \E c \in Clients : \E k \in Keys : PessimisticLock(c, k)
  \/ \E c \in Clients : CommitTransaction(c)
  \/ \E c \in Clients : AbortTransaction(c)

Spec == Init /\ [][Next]_<<clientState, keyLocks, keyValues, transactionLog, messageTimestamps>>

THEOREM Spec => []TypeInvariant
=============================================================================