```
MODULE DistributedTransactionConfig
EXTENDS DistributedTransaction,
       Integers,
       FiniteSets

CONSTANTS Keys, Clients, ClientClass, ReadKeys, WriteKeys, PrimaryKey

VARIABLES state, msgQueue, clientState, lockState, ts

Init ==
  /\ state = << >>
  /\ msgQueue = << >>
  /\ clientState = [c \in Clients |-> << >>]
  /\ lockState = [k \in Keys |-> None]
  /\ ts = 0

Next ==
  DistributedTransaction!Next

Spec == Init /\ [][Next]_state

TypeOK == 
  /\ Keys = {k1, k2}
  /\ Clients = {c1, c2}
  /\ ClientClass = [c1 |-> "pessimistic", c2 |-> "optimistic"]
  /\ ReadKeys = [c1 |-> {}, c2 |-> {k1, k2}]
  /\ WriteKeys = [c1 |-> {k1, k2}, c2 |-> {k1, k2}]
  /\ PrimaryKey = [c1 |-> k1, c2 |-> k1]

UniqueCommitOrAbort == 
  \A c \in Clients : 
    (state[c] = "Committed") \/ (state[c] = "Aborted")

CommitConsistency == 
  \A c \in Clients : 
    (state[c] = "Committed") => (\A k \in WriteKeys[c] : lockState[k] = c)

AbortConsistency == 
  \A c \in Clients : 
    (state[c] = "Aborted") => (\A k \in WriteKeys[c] : lockState[k] = None)

WriteConsistency == 
  \A c \in Clients, k \in WriteKeys[c] : 
    (lockState[k] = c) => (state[c] = "Committed")

UniqueWrite == 
  \A k \in Keys : 
    ~(\E c1, c2 \in Clients : c1 # c2 /\ lockState[k] = c1 /\ lockState[k] = c2)

UniqueLockOrWrite == 
  \A k \in Keys : 
    ~(\E c1, c2 \in Clients : c1 # c2 /\ (lockState[k] = c1 \/ state[c1] = "Committed") /\ (lockState[k] = c2 \/ state[c2] = "Committed"))

OptimisticReadSnapshotIsolation == 
  \A c \in {c \in Clients : ClientClass[c] = "optimistic"} : 
    (\A k \in ReadKeys[c] : lockState[k] # None) => (state[c] = "Aborted")

PessimisticReadSnapshotIsolation == 
  \A c \in {c \in Clients : ClientClass[c] = "pessimistic"} : 
    (\A k \in ReadKeys[c] : lockState[k] # None) => (state[c] = "Aborted")

MsgTsConsistency == 
  \A msg \in msgQueue : 
    msg.ts <= ts

THEOREM Spec => []TypeOK
THEOREM Spec => []UniqueCommitOrAbort
THEOREM Spec => []CommitConsistency
THEOREM Spec => []AbortConsistency
THEOREM Spec => []WriteConsistency
THEOREM Spec => []UniqueWrite
THEOREM Spec => []UniqueLockOrWrite
THEOREM Spec => []OptimisticReadSnapshotIsolation
THEOREM Spec => []PessimisticReadSnapshotIsolation
THEOREM Spec => []MsgTsConsistency

Fairness == SF_VARIABLES(state, msgQueue, clientState, lockState, ts)
```