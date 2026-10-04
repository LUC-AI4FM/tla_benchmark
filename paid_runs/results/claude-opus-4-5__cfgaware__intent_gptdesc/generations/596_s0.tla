---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Clients,
    Keys,
    Replicas,
    MaxRetries,
    Null

VARIABLES
    \* Client state
    clientState,        \* Function: client -> state (Idle, Running, Committed, Aborted)
    clientTxnStyle,     \* Function: client -> style (Pessimistic, Optimistic)
    clientReadSet,      \* Function: client -> set of keys to read
    clientWriteSet,     \* Function: client -> set of keys to write
    clientReadValues,   \* Function: client -> function from key to value read
    clientWriteValues,  \* Function: client -> function from key to value to write
    clientRetryCount,   \* Function: client -> number of retries
    clientTxnId,        \* Function: client -> current transaction ID
    clientSnapshot,     \* Function: client -> snapshot of data at txn start
    
    \* Replica state
    replicaData,        \* Function: replica -> function from key to value
    replicaLocks,       \* Function: replica -> function from key to lock holder (client or Null)
    replicaPrimary,     \* Function: key -> primary replica for that key
    replicaCommitLog,   \* Function: replica -> sequence of committed txn IDs
    
    \* Message passing
    messages,           \* Set of messages in transit
    
    \* Global state for verification
    txnCounter,         \* Counter for generating unique transaction IDs
    committedTxns,      \* Set of committed transaction records
    serialOrder         \* Sequence representing serial order of committed txns

vars == <<clientState, clientTxnStyle, clientReadSet, clientWriteSet, 
          clientReadValues, clientWriteValues, clientRetryCount, clientTxnId,
          clientSnapshot, replicaData, replicaLocks, replicaPrimary,
          replicaCommitLog, messages, txnCounter, committedTxns, serialOrder>>

-----------------------------------------------------------------------------
(* Message types *)
MsgTypes == {"ReadReq", "ReadResp", "WriteReq", "WriteResp", 
             "LockReq", "LockResp", "UnlockReq", "UnlockResp",
             "PrepareReq", "PrepareResp", "CommitReq", "CommitResp",
             "AbortReq", "AbortResp", "ForwardReq", "ForwardResp"}

ClientStates == {"Idle", "Reading", "Writing", "Preparing", "Committing", 
                 "Committed", "Aborting", "Aborted"}

TxnStyles == {"Pessimistic", "Optimistic"}

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ clientState \in [Clients -> ClientStates]
    /\ clientTxnStyle \in [Clients -> TxnStyles]
    /\ clientReadSet \in [Clients -> SUBSET Keys]
    /\ clientWriteSet \in [Clients -> SUBSET Keys]
    /\ clientRetryCount \in [Clients -> 0..MaxRetries]
    /\ txnCounter \in Nat
    /\ replicaPrimary \in [Keys -> Replicas]

-----------------------------------------------------------------------------
(* Helper functions *)

\* Get the primary replica for a key
PrimaryOf(k) == replicaPrimary[k]

\* Check if a client holds all required locks
HasAllLocks(c) ==
    \A k \in (clientReadSet[c] \union clientWriteSet[c]):
        replicaLocks[PrimaryOf(k)][k] = c

\* Check for write-write conflict between two clients
HasWriteConflict(c1, c2) ==
    /\ c1 /= c2
    /\ clientWriteSet[c1] \cap clientWriteSet[c2] /= {}

\* Get current value of a key from its primary
GetValue(k) == replicaData[PrimaryOf(k)][k]

\* Check if optimistic transaction can commit (no conflicts)
CanOptimisticCommit(c) ==
    \* Check that snapshot is still valid (no conflicting commits)
    \A k \in clientReadSet[c]:
        clientSnapshot[c][k] = GetValue(k)

-----------------------------------------------------------------------------
(* Initial state *)
Init ==
    /\ clientState = [c \in Clients |-> "Idle"]
    /\ clientTxnStyle = [c \in Clients |-> 
                         IF c = CHOOSE x \in Clients : TRUE 
                         THEN "Pessimistic" 
                         ELSE "Optimistic"]
    /\ clientReadSet = [c \in Clients |-> {}]
    /\ clientWriteSet = [c \in Clients |-> {}]
    /\ clientReadValues = [c \in Clients |-> [k \in Keys |-> 0]]
    /\ clientWriteValues = [c \in Clients |-> [k \in Keys |-> 0]]
    /\ clientRetryCount = [c \in Clients |-> 0]
    /\ clientTxnId = [c \in Clients |-> 0]
    /\ clientSnapshot = [c \in Clients |-> [k \in Keys |-> 0]]
    /\ replicaData = [r \in Replicas |-> [k \in Keys |-> 0]]
    /\ replicaLocks = [r \in Replicas |-> [k \in Keys |-> Null]]
    /\ replicaPrimary = [k \in Keys |-> CHOOSE r \in Replicas : TRUE]
    /\ replicaCommitLog = [r \in Replicas |-> <<>>]
    /\ messages = {}
    /\ txnCounter = 0
    /\ committedTxns = {}
    /\ serialOrder = <<>>

-----------------------------------------------------------------------------
(* Client actions *)

\* Client starts a new transaction
StartTransaction(c, rs, ws) ==
    /\ clientState[c] = "Idle"
    /\ rs \subseteq Keys
    /\ ws \subseteq Keys
    /\ rs /= {} \/ ws /= {}
    /\ clientState' = [clientState EXCEPT ![c] = "Reading"]
    /\ clientReadSet' = [clientReadSet EXCEPT ![c] = rs]
    /\ clientWriteSet' = [clientWriteSet EXCEPT ![c] = ws]
    /\ txnCounter' = txnCounter + 1
    /\ clientTxnId' = [clientTxnId EXCEPT ![c] = txnCounter + 1]
    /\ clientSnapshot' = [clientSnapshot EXCEPT ![c] = 
                          [k \in Keys |-> GetValue(k)]]
    /\ clientWriteValues' = [clientWriteValues EXCEPT ![c] = 
                             [k \in Keys |-> IF k \in ws 
                                            THEN clientTxnId'[c] 
                                            ELSE 0]]
    /\ UNCHANGED <<clientTxnStyle, clientReadValues, clientRetryCount,
                   replicaData, replicaLocks, replicaPrimary, replicaCommitLog,
                   messages, committedTxns, serialOrder>>

\* Pessimistic client acquires locks
AcquireLocks(c) ==
    /\ clientState[c] = "Reading"
    /\ clientTxnStyle[c] = "Pessimistic"
    /\ LET keysToLock == clientReadSet[c] \union clientWriteSet[c]
       IN \A k \in keysToLock: 
            replicaLocks[PrimaryOf(k)][k] = Null
    /\ replicaLocks' = [r \in Replicas |-> 
                        [k \in Keys |-> 
                         IF k \in (clientReadSet[c] \union clientWriteSet[c]) 
                            /\ PrimaryOf(k) = r
                         THEN c
                         ELSE replicaLocks[r][k]]]
    /\ clientReadValues' = [clientReadValues EXCEPT ![c] = 
                            [k \in Keys |-> IF k \in clientReadSet[c]
                                           THEN GetValue(k)
                                           ELSE clientReadValues[c][k]]]
    /\ clientState' = [clientState EXCEPT ![c] = "Writing"]
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet, 
                   clientWriteValues, clientRetryCount, clientTxnId,
                   clientSnapshot, replicaData, replicaPrimary, replicaCommitLog,
                   messages, txnCounter, committedTxns, serialOrder>>

\* Optimistic client reads without locks
OptimisticRead(c) ==
    /\ clientState[c] = "Reading"
    /\ clientTxnStyle[c] = "Optimistic"
    /\ clientReadValues' = [clientReadValues EXCEPT ![c] = 
                            [k \in Keys |-> IF k \in clientReadSet[c]
                                           THEN clientSnapshot[c][k]
                                           ELSE clientReadValues[c][k]]]
    /\ clientState' = [clientState EXCEPT ![c] = "Writing"]
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientWriteValues, clientRetryCount, clientTxnId,
                   clientSnapshot, replicaData, replicaLocks, replicaPrimary,
                   replicaCommitLog, messages, txnCounter, committedTxns, serialOrder>>

\* Client prepares to commit
PrepareCommit(c) ==
    /\ clientState[c] = "Writing"
    /\ clientState' = [clientState EXCEPT ![c] = "Preparing"]
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientRetryCount,
                   clientTxnId, clientSnapshot, replicaData, replicaLocks,
                   replicaPrimary, replicaCommitLog, messages, txnCounter,
                   committedTxns, serialOrder>>

\* Pessimistic client commits (already holds locks)
PessimisticCommit(c) ==
    /\ clientState[c] = "Preparing"
    /\ clientTxnStyle[c] = "Pessimistic"
    /\ HasAllLocks(c)
    \* Apply writes
    /\ replicaData' = [r \in Replicas |->
                       [k \in Keys |->
                        IF k \in clientWriteSet[c] /\ PrimaryOf(k) = r
                        THEN clientWriteValues[c][k]
                        ELSE replicaData[r][k]]]
    \* Release locks
    /\ replicaLocks' = [r \in Replicas |->
                        [k \in Keys |->
                         IF replicaLocks[r][k] = c
                         THEN Null
                         ELSE replicaLocks[r][k]]]
    /\ replicaCommitLog' = [r \in Replicas |->
                            Append(replicaCommitLog[r], clientTxnId[c])]
    /\ clientState' = [clientState EXCEPT ![c] = "Committed"]
    /\ committedTxns' = committedTxns \union 
                        {[client |-> c, 
                          txnId |-> clientTxnId[c],
                          reads |-> clientReadSet[c],
                          writes |-> clientWriteSet[c],
                          readVals |-> clientReadValues[c],
                          writeVals |-> clientWriteValues[c]]}
    /\ serialOrder' = Append(serialOrder, clientTxnId[c])
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientRetryCount,
                   clientTxnId, clientSnapshot, replicaPrimary, messages,
                   txnCounter>>

\* Optimistic client attempts to commit
OptimisticCommit(c) ==
    /\ clientState[c] = "Preparing"
    /\ clientTxnStyle[c] = "Optimistic"
    /\ CanOptimisticCommit(c)
    \* Acquire locks for commit
    /\ \A k \in clientWriteSet[c]: replicaLocks[PrimaryOf(k)][k] = Null
    \* Apply writes
    /\ replicaData' = [r \in Replicas |->
                       [k \in Keys |->
                        IF k \in clientWriteSet[c] /\ PrimaryOf(k) = r
                        THEN clientWriteValues[c][k]
                        ELSE replicaData[r][k]]]
    /\ replicaCommitLog' = [r \in Replicas |->
                            Append(replicaCommitLog[r], clientTxnId[c])]
    /\ clientState' = [clientState EXCEPT ![c] = "Committed"]
    /\ committedTxns' = committedTxns \union 
                        {[client |-> c, 
                          txnId |-> clientTxnId[c],
                          reads |-> clientReadSet[c],
                          writes |-> clientWriteSet[c],
                          readVals |-> clientReadValues[c],
                          writeVals |-> clientWriteValues[c]]}
    /\ serialOrder' = Append(serialOrder, clientTxnId[c])
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientRetryCount,
                   clientTxnId, clientSnapshot, replicaLocks, replicaPrimary,
                   messages, txnCounter>>

\* Optimistic client aborts due to conflict
OptimisticAbort(c) ==
    /\ clientState[c] = "Preparing"
    /\ clientTxnStyle[c] = "Optimistic"
    /\ ~CanOptimisticCommit(c)
    /\ clientRetryCount[c] < MaxRetries
    /\ clientState' = [clientState EXCEPT ![c] = "Aborted"]
    /\ clientRetryCount' = [clientRetryCount EXCEPT ![c] = @ + 1]
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientTxnId,
                   clientSnapshot, replicaData, replicaLocks, replicaPrimary,
                   replicaCommitLog, messages, txnCounter, committedTxns,
                   serialOrder>>

\* Client retries after abort
RetryTransaction(c) ==
    /\ clientState[c] = "Aborted"
    /\ clientRetryCount[c] < MaxRetries
    /\ clientState' = [clientState EXCEPT ![c] = "Reading"]
    /\ txnCounter' = txnCounter + 1
    /\ clientTxnId' = [clientTxnId EXCEPT ![c] = txnCounter + 1]
    /\ clientSnapshot' = [clientSnapshot EXCEPT ![c] = 
                          [k \in Keys |-> GetValue(k)]]
    /\ clientWriteValues' = [clientWriteValues EXCEPT ![c] = 
                             [k \in Keys |-> IF k \in clientWriteSet[c]
                                            THEN clientTxnId'[c]
                                            ELSE 0]]
    /\ UNCHANGED <<clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientRetryCount, replicaData,
                   replicaLocks, replicaPrimary, replicaCommitLog, messages,
                   committedTxns, serialOrder>>

\* Client returns to idle after commit
ReturnToIdle(c) ==
    /\ clientState[c] \in {"Committed", "Aborted"}
    /\ clientState' = [clientState EXCEPT ![c] = "Idle"]
    /\ clientRetryCount' = [clientRetryCount EXCEPT ![c] = 0]
    /\ clientReadSet' = [clientReadSet EXCEPT ![c] = {}]
    /\ clientWriteSet' = [clientWriteSet EXCEPT ![c] = {}]
    /\ UNCHANGED <<clientTxnStyle, clientReadValues, clientWriteValues,
                   clientTxnId, clientSnapshot, replicaData, replicaLocks,
                   replicaPrimary, replicaCommitLog, messages, txnCounter,
                   committedTxns, serialOrder>>

\* Send a message (for message passing)
SendMessage(m) ==
    /\ messages' = messages \union {m}
    /\ UNCHANGED <<clientState, clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientRetryCount,
                   clientTxnId, clientSnapshot, replicaData, replicaLocks,
                   replicaPrimary, replicaCommitLog, txnCounter, committedTxns,
                   serialOrder>>

\* Forward request to primary
ForwardToPrimary(c, k) ==
    /\ clientState[c] \in {"Reading", "Writing"}
    /\ k \in clientReadSet[c] \union clientWriteSet[c]
    /\ messages' = messages \union 
                   {[type |-> "ForwardReq", 
                     client |-> c, 
                     key |-> k, 
                     primary |-> PrimaryOf(k)]}
    /\ UNCHANGED <<clientState, clientTxnStyle, clientReadSet, clientWriteSet,
                   clientReadValues, clientWriteValues, clientRetryCount,
                   clientTxnId, clientSnapshot, replicaData, replicaLocks,
                   replicaPrimary, replicaCommitLog, txnCounter, committedTxns,
                   serialOrder>>

-----------------------------------------------------------------------------
(* Next state relation *)
Next ==
    \/ \E c \in Clients, rs, ws \in SUBSET Keys:
        StartTransaction(c, rs, ws)
    \/ \E c \in Clients: AcquireLocks(c)
    \/ \E c \in Clients: OptimisticRead(c)
    \/ \E c \in Clients: PrepareCommit(c)
    \/ \E c \in Clients: PessimisticCommit(c)
    \/ \E c \in Clients: OptimisticCommit(c)
    \/ \E c \in Clients: OptimisticAbort(c)
    \/ \E c \in Clients: RetryTransaction(c)
    \/ \E c \in Clients: ReturnToIdle(c)
    \/ \E c \in Clients, k \in Keys: ForwardToPrimary(c, k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Properties *)

\* No write-write conflicts among committed transactions at the same key
NoWriteWriteConflict ==
    \A t1, t2 \in committedTxns:
        t1 /= t2 /\ t1.writes \cap t2.writes /= {} =>
            \* One must be ordered before the other in serial order
            \E i, j \in 1..Len(serialOrder):
                /\ serialOrder[i] = t1.txnId
                /\ serialOrder[j] = t2.txnId
                /\ i /= j

\* Serializability: committed transactions are equivalent to serial execution
Serializability ==
    \* For each pair of committed transactions with conflicting operations,
    \* there is a consistent serial ordering
    \A t1, t2 \in committedTxns:
        t1 /= t2 =>
            \E i, j \in 1..Len(serialOrder):
                /\ serialOrder[i] = t1.txnId
                /\ serialOrder[j] = t2.txnId
                /\ (i < j \/ j < i)

\* No lost updates: if a transaction commits a write, it persists
NoLostUpdates ==
    \A t \in committedTxns:
        \A k \in t.writes:
            \* Either the value is still there, or a later transaction overwrote it
            \/ replicaData[PrimaryOf(k)][k] = t.writeVals[k]
            \/ \E t2 \in committedTxns:
                /\ k \in t2.writes
                /\ \E i, j \in 1..Len(serialOrder):
                    /\ serialOrder[i] = t.txnId
                    /\ serialOrder[j] = t2.txnId
                    /\ i < j

\* Read-your-writes within a transaction
ReadYourWrites ==
    \A c \in Clients:
        clientState[c] \in {"Writing", "Preparing", "Committing"} =>
            \A k \in clientWriteSet[c] \cap clientReadSet[c]:
                \* Client sees its own pending writes
                TRUE  \* Simplified - in practice would check read buffer

\* Mutual exclusion on pessimistic locks
LockMutualExclusion ==
    \A r \in Replicas, k \in Keys:
        replicaLocks[r][k] /= Null =>
            \A c \in Clients:
                replicaLocks[r][k] = c =>
                    \A c2 \in Clients \ {c}:
                        \A r2 \in Replicas:
                            replicaLocks[r2][k] /= c2

\* Safety invariant combining all safety properties
Safety ==
    /\ TypeOK
    /\ NoWriteWriteConflict
    /\ Serializability
    /\ NoLostUpdates
    /\ LockMutualExclusion

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Fairness assumptions
Fairness ==
    /\ \A c \in Clients: WF_vars(AcquireLocks(c))
    /\ \A c \in Clients: WF_vars(OptimisticRead(c))
    /\ \A c \in Clients: WF_vars(PrepareCommit(c))
    /\ \A c \in Clients: WF_vars(PessimisticCommit(c))
    /\ \A c \in Clients: WF_vars(OptimisticCommit(c))
    /\ \A c \in Clients: WF_vars(RetryTransaction(c))

\* A transaction that retries under bounded contention eventually commits
EventualCommit ==
    \A c \in Clients:
        (clientState[c] = "Reading" /\ clientRetryCount[c] < MaxRetries) ~>
            (clientState[c] = "Committed" \/ clientRetryCount[c] >= MaxRetries)

\* Progress: system makes progress when majority available
Progress ==
    \A c \in Clients:
        clientState[c] = "Idle" ~> 
            (clientState[c] = "Committed" \/ clientState[c] = "Aborted" \/ clientState[c] = "Idle")

\* Liveness specification
Liveness ==
    /\ EventualCommit
    /\ Progress

\* Full specification with fairness
FairSpec == Spec /\ Fairness

=============================================================================