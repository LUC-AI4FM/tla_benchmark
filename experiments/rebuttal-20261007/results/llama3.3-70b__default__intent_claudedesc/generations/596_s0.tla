```tla
MODULE DistributedTransactionSystem

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys, Clients, PrimaryKeys
VARIABLES clientState, keyState, transactionState, messageTimestamps,
          reads, writes, locks, commits, aborts

Init ==
  /\ clientState \in [Clients |-> {"status" |-> "idle", "keysToRead" |-> {}, "keysToWrite" |-> {}}]
  /\ keyState \in [Keys |-> {"value" |-> 0, "lockedBy" |-> None}]
  /\ transactionState \in [Clients |-> {"transactionId" |-> 0, "committed" |-> FALSE, "aborted" |-> FALSE}]
  /\ messageTimestamps \in [Clients |-> 0]
  /\ reads = {}
  /\ writes = {}
  /\ locks = {}
  /\ commits = {}
  /\ aborts = {}

Next ==
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "idle"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "reading"]]
        /\ reads' = reads \cup {c |-> {}}
      ELSE
        /\ clientState' = clientState
        /\ reads' = reads
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "reading"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "locking"]]
        /\ locks' = locks \cup {c |-> {}}
      ELSE
        /\ clientState' = clientState
        /\ locks' = locks
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "locking"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "writing"]]
        /\ writes' = writes \cup {c |-> {}}
      ELSE
        /\ clientState' = clientState
        /\ writes' = writes
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "writing"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "committing"]]
        /\ commits' = commits \cup {c}
      ELSE
        /\ clientState' = clientState
        /\ commits' = commits
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "committing"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "committed"]]
        /\ transactionState' = [transactionState EXCEPT ![c] = ["committed" |-> TRUE]]
      ELSE
        /\ clientState' = clientState
        /\ transactionState' = transactionState
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "writing"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "aborting"]]
        /\ aborts' = aborts \cup {c}
      ELSE
        /\ clientState' = clientState
        /\ aborts' = aborts
  /\ IF \E c \in Clients :
        /\ clientState[c]["status"] = "aborting"
        /\ clientState' = [clientState EXCEPT ![c] = ["status" |-> "aborted"]]
        /\ transactionState' = [transactionState EXCEPT ![c] = ["aborted" |-> TRUE]]
      ELSE
        /\ clientState' = clientState
        /\ transactionState' = transactionState
  /\ keyState' = keyState
  /\ messageTimestamps' = messageTimestamps

Spec ==
  /\ Init
  /\ [][Next]_clientState, keyState, transactionState, messageTimestamps,
       reads, writes, locks, commits, aborts
  /\ WF_vars(Next, clientState, keyState, transactionState, messageTimestamps,
             reads, writes, locks, commits, aborts)
  /\ SF_vars(Next, clientState, keyState, transactionState, messageTimestamps,
             reads, writes, locks, commits, aborts)

THEOREM Spec => [](\A c \in Clients : transactionState[c]["committed"] \/ transactionState[c]["aborted"])
THEOREM Spec => [](\A k \in Keys : \A c1, c2 \in Clients : keyState[k]["lockedBy"] = c1 /\ keyState[k]["lockedBy"] = c2 => c1 = c2)
THEOREM Spec => [](\A c \in Clients : clientState[c]["status"] = "committed" => \A k \in Keys : reads[c][k] = writes[c][k])
THEOREM Spec => [](\A c \in Clients : clientState[c]["status"] = "aborted" => \A k \in Keys : reads[c][k] = {})
THEOREM Spec => [](\A k \in Keys : \A c1, c2 \in Clients : writes[c1][k] /= {} /\ writes[c2][k] /= {} => c1 = c2)
THEOREM Spec => [](\A c \in Clients : clientState[c]["status"] = "optimistic" => \A k \in Keys : reads[c][k] = keyState[k]["value"])
THEOREM Spec => [](\A c \in Clients : clientState[c]["status"] = "pessimistic" => \A k \in Keys : reads[c][k] = keyState[k]["value"])

=============================================================================
```
Note: The above TLA+ specification models the distributed transaction system with both optimistic and pessimistic clients. It includes variables to track the state of each client, key, and transaction, as well as the messages exchanged between them. The `Next` action describes the possible transitions between these states, while the `Spec` formula defines the correctness properties that must be satisfied by the system. The `THEOREM` statements specify the desired safety and liveness properties.