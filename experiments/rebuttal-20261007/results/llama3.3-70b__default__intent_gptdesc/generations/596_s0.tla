```
MODULE DistributedKeyValueStore

EXTENDS Integers, Sequences, TLC

CONSTANTS
  Clients,
  Keys,
  ReadSets,
  WriteSets,
  PrimaryMapping,
  MessageTypes,
  Retries

VARIABLES
  clientState,
  replicaState,
  transactionLog,
  messageQueue,
  retryCount

Init ==
  /\ clientState = [c \in Clients |-> "idle"]
  /\ replicaState = [k \in Keys |-> "initial"]
  /\ transactionLog = <<>>
  /\ messageQueue = <<>>
  /\ retryCount = [c \in Clients |-> 0]

Next ==
  \/ \E c \in Clients :
      /\ clientState[c] = "idle"
      /\ \E rs \in ReadSets, ws \in WriteSets :
          /\ c = "client1" => clientState' = [clientState EXCEPT ![c] = "pessimistic"]
          /\ c = "client2" => clientState' = [clientState EXCEPT ![c] = "optimistic"]
          /\ replicaState' = replicaState
          /\ transactionLog' = Append(transactionLog, <<c, rs, ws>>)
          /\ messageQueue' = Append(messageQueue, <<c, "start", PrimaryMapping[rs \cup ws]>>)
          /\ retryCount' = retryCount
  \/ \E c \in Clients :
      /\ clientState[c] = "pessimistic"
      /\ \E m \in messageQueue :
          /\ m[1] = c
          /\ m[2] = "start"
          /\ replicaState' = [replicaState EXCEPT ![PrimaryMapping[m[3]]] = "locked"]
          /\ transactionLog' = transactionLog
          /\ messageQueue' = Tail(messageQueue)
          /\ retryCount' = retryCount
  \/ \E c \in Clients :
      /\ clientState[c] = "optimistic"
      /\ \E m \in messageQueue :
          /\ m[1] = c
          /\ m[2] = "start"
          /\ replicaState' = replicaState
          /\ transactionLog' = Append(transactionLog, <<c, ReadSets[c], WriteSets[c]>>)
          /\ messageQueue' = Append(messageQueue, <<c, "read", PrimaryMapping[ReadSets[c]]>>)
          /\ retryCount' = [retryCount EXCEPT ![c] = retryCount[c] + 1]
  \/ \E c \in Clients :
      /\ clientState[c] = "optimistic"
      /\ \E m \in messageQueue :
          /\ m[1] = c
          /\ m[2] = "read"
          /\ replicaState' = [replicaState EXCEPT ![PrimaryMapping[m[3]]] = "read"]
          /\ transactionLog' = transactionLog
          /\ messageQueue' = Tail(messageQueue)
          /\ retryCount' = retryCount
  \/ \E c \in Clients :
      /\ clientState[c] = "optimistic"
      /\ \E m \in messageQueue :
          /\ m[1] = c
          /\ m[2] = "write"
          /\ replicaState' = [replicaState EXCEPT ![PrimaryMapping[m[3]]] = "written"]
          /\ transactionLog' = Append(transactionLog, <<c, ReadSets[c], WriteSets[c]>>)
          /\ messageQueue' = Tail(messageQueue)
          /\ retryCount' = retryCount
  \/ \E c \in Clients :
      /\ clientState[c] = "optimistic"
      /\ retryCount[c] >= Retries
      /\ replicaState' = replicaState
      /\ transactionLog' = transactionLog
      /\ messageQueue' = <<>>
      /\ retryCount' = [retryCount EXCEPT ![c] = 0]

Spec ==
  /\ Init
  /\ [][Next]_clientState, replicaState, transactionLog, messageQueue, retryCount
  /\ WF_vars(Next, clientState, replicaState, transactionLog, messageQueue, retryCount)
  /\ Serializability == \A t1, t2 \in transactionLog :
      \/ t1 = t2
      \/ (t1[1] # t2[1]) /\ (t1[3] \cap t2[3] = {})
  /\ NoLostUpdates == \A t \in transactionLog :
      t[2] \subseteq t[3]
  /\ ReadYourWrites == \A c \in Clients, rs \in ReadSets :
      \E ws \in WriteSets : (rs \cap ws = {}) => (c = "client1" => clientState[c] = "pessimistic")
  /\ Progress == <> \E c \in Clients : clientState[c] = "committed"

THEOREM Spec => []Serializability
THEOREM Spec => []NoLostUpdates
THEOREM Spec => []ReadYourWrites
THEOREM Spec => Progress
```