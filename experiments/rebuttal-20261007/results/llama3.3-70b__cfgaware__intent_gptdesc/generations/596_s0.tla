---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
  ClientSet,
  KeySet,
  ReadSets,
  WriteSets,
  PrimaryMapping

VARIABLES
  clientState,
  replicaState,
  transactionLog,
  messageQueue

Macros == (* Macros for convenience *)
  IsCommitted(txn) == txn \in DOMAIN transactionLog,
  GetTransactionLog(txn) == transactionLog[txn],
  GetReadSet(client) == ReadSets[client],
  GetWriteSet(client) == WriteSets[client],
  GetPrimary(key) == PrimaryMapping[key]

TypeInvariants == (* Type invariants *)
  /\
  clientState \in [ClientSet -> {"idle", "active"}]
  /\ replicaState \in [KeySet -> {<<"value": Int>>}]
  /\ transactionLog \in Seq(ClientSet) -> (Seq(KeySet) \X Seq(Int))
  /\ messageQueue \in Seq(<<"client": ClientSet, "key": KeySet, "type": {"read", "write"}, "value": Int>>)

Init == (* Initial state *)
  /\
  clientState = [c \in ClientSet |-> "idle"]
  /\ replicaState = [k \in KeySet |-> <<>>
  /\ transactionLog = <<>>
  /\ messageQueue = <<>>

Next == (* Next-state relation *)
  /\ \E c \in ClientSet, k \in KeySet:
      IF clientState[c] = "idle"
      THEN
        /\ clientState' = [clientState EXCEPT ![c] = "active"]
        /\ replicaState' = replicaState
        /\ transactionLog' = Append(transactionLog, <<c, {}>>)
        /\ messageQueue' = Append(messageQueue, <<{"client": c, "key": k, "type": "read", "value": 0}>>)
      ELSE
        /\ clientState' = clientState
        /\ replicaState' = IF messageQueue # <<>>
                  THEN [replicaState EXCEPT ![Head(messageQueue)."key"] = 
                        IF Head(messageQueue)."type" = "write"
                        THEN <<{"value": Head(messageQueue)."value"}>>
                        ELSE replicaState[Head(messageQueue)."key"]]
                  ELSE replicaState
        /\ transactionLog' = IF messageQueue # <<>>
                            THEN Append(transactionLog, <<Head(messageQueue)."client", {Head(messageQueue)."key" : Head(messageQueue)."value"}>>)
                            ELSE transactionLog
        /\ messageQueue' = Tail(messageQueue)

PessimisticLocking == (* Pessimistic locking *)
  /\ \A c \in ClientSet:
      IF clientState[c] = "active"
      THEN
        /\ \E k \in GetWriteSet(c):
            replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>

OptimisticConcurrencyControl == (* Optimistic concurrency control *)
  /\ \A c \in ClientSet:
      IF clientState[c] = "active"
      THEN
        /\ \E k \in GetReadSet(c):
            replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>
        /\ \E k \in GetWriteSet(c):
            replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>

Serializability == (* Serializability *)
  /\ \A txns \in Seq(ClientSet):
      IsCommitted(txns) => 
        /\ \A i, j \in DOMAIN txns:
            i # j => GetWriteSet(txns[i]) \cap GetWriteSet(txns[j]) = {}

NoLostUpdates == (* No lost updates *)
  /\ \A c \in ClientSet, k \in KeySet:
      IF clientState[c] = "active"
      THEN
        /\ replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>

ReadYourWrites == (* Read-your-writes *)
  /\ \A c \in ClientSet, k \in KeySet:
      IF clientState[c] = "active"
      THEN
        /\ replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>

Liveness == (* Liveness *)
  /\ \A c \in ClientSet:
      IF clientState[c] = "active"
      THEN
        /\ \E k \in GetWriteSet(c):
            /\ replicaState'[k] = <<{"value": transactionLog[GetTransactionLog(c)].k}>>

THEOREM Spec => []Liveness

=============================================================================