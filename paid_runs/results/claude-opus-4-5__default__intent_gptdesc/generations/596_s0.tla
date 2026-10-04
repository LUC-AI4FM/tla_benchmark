---------------------------- MODULE DistributedTxnKVStore ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Client1,        \* Pessimistic client
    Client2,        \* Optimistic client
    Key1,           \* First key
    Key2,           \* Second key
    Primary1,       \* Primary replica for Key1
    Primary2,       \* Primary replica for Key2
    MaxRetries,     \* Bounded retries for optimistic transactions
    MaxValue        \* Maximum value for keys

VARIABLES
    \* Key-value store state
    kvStore,            \* Function: Key -> Value
    kvVersion,          \* Function: Key -> Version number
    
    \* Lock state (for pessimistic locking)
    locks,              \* Function: Key -> {None, Client1, Client2}
    
    \* Transaction state
    txnState,           \* Function: Client -> {Idle, Started, Reading, Writing, Preparing, Committed, Aborted}
    txnReadSet,         \* Function: Client -> Set of keys to read
    txnWriteSet,        \* Function: Client -> Set of keys to write
    txnReadValues,      \* Function: Client -> (Key -> Value) - values read in transaction
    txnWriteValues,     \* Function: Client -> (Key -> Value) - values to write
    txnStartVersion,    \* Function: Client -> Version at transaction start (for optimistic)
    txnRetryCount,      \* Function: Client -> Number of retries (for optimistic)
    
    \* Message channels
    messages,           \* Set of messages in transit
    
    \* Commit log for serializability checking
    commitLog,          \* Sequence of committed transactions
    
    \* Global version counter
    globalVersion

Clients == {Client1, Client2}
Keys == {Key1, Key2}
Primaries == {Primary1, Primary2}
Values == 0..MaxValue

\* Primary mapping: each key has an assigned primary
KeyToPrimary == [k \in Keys |-> IF k = Key1 THEN Primary1 ELSE Primary2]

\* Define read and write sets for each client
Client1ReadSet == {Key1}
Client1WriteSet == {Key1, Key2}
Client2ReadSet == {Key1, Key2}
Client2WriteSet == {Key2}

GetClientReadSet(c) == IF c = Client1 THEN Client1ReadSet ELSE Client2ReadSet
GetClientWriteSet(c) == IF c = Client1 THEN Client1WriteSet ELSE Client2WriteSet

\* Transaction styles
IsPessimistic(c) == c = Client1
IsOptimistic(c) == c = Client2

\* Message types
MsgType == {"ReadRequest", "ReadResponse", "WriteRequest", "WriteResponse", 
            "LockRequest", "LockResponse", "PrepareRequest", "PrepareResponse",
            "CommitRequest", "CommitResponse", "AbortRequest", "AbortResponse"}

TypeOK ==
    /\ kvStore \in [Keys -> Values]
    /\ kvVersion \in [Keys -> Nat]
    /\ locks \in [Keys -> Clients \cup {NONE}]
    /\ txnState \in [Clients -> {"Idle", "Started", "Locking", "Reading", "Writing", "Preparing", "Committed", "Aborted"}]
    /\ txnReadSet \in [Clients -> SUBSET Keys]
    /\ txnWriteSet \in [Clients -> SUBSET Keys]
    /\ txnReadValues \in [Clients -> [Keys -> Values \cup {NONE}]]
    /\ txnWriteValues \in [Clients -> [Keys -> Values \cup {NONE}]]
    /\ txnStartVersion \in [Clients -> Nat]
    /\ txnRetryCount \in [Clients -> 0..MaxRetries]
    /\ globalVersion \in Nat

NONE == CHOOSE x : x \notin (Clients \cup Keys \cup Primaries \cup Values)

Init ==
    /\ kvStore = [k \in Keys |-> 0]
    /\ kvVersion = [k \in Keys |-> 0]
    /\ locks = [k \in Keys |-> NONE]
    /\ txnState = [c \in Clients |-> "Idle"]
    /\ txnReadSet = [c \in Clients |-> {}]
    /\ txnWriteSet = [c \in Clients |-> {}]
    /\ txnReadValues = [c \in Clients |-> [k \in Keys |-> NONE]]
    /\ txnWriteValues = [c \in Clients |-> [k \in Keys |-> NONE]]
    /\ txnStartVersion = [c \in Clients |-> 0]
    /\ txnRetryCount = [c \in Clients |-> 0]
    /\ messages = {}
    /\ commitLog = <<>>
    /\ globalVersion = 0

\* Start a transaction
StartTransaction(c) ==
    /\ txnState[c] = "Idle"
    /\ txnState' = [txnState EXCEPT ![c] = "Started"]
    /\ txnReadSet' = [txnReadSet EXCEPT ![c] = GetClientReadSet(c)]
    /\ txnWriteSet' = [txnWriteSet EXCEPT ![c] = GetClientWriteSet(c)]
    /\ txnReadValues' = [txnReadValues EXCEPT ![c] = [k \in Keys |-> NONE]]
    /\ txnWriteValues' = [txnWriteValues EXCEPT ![c] = [k \in Keys |-> NONE]]
    /\ txnStartVersion' = [txnStartVersion EXCEPT ![c] = globalVersion]
    /\ UNCHANGED <<kvStore, kvVersion, locks, messages, commitLog, globalVersion, txnRetryCount>>

\* Pessimistic: Acquire locks before reading/writing
AcquireLocks(c) ==
    /\ IsPessimistic(c)
    /\ txnState[c] = "Started"
    /\ LET keysNeeded == txnReadSet[c] \cup txnWriteSet[c]
           canAcquire == \A k \in keysNeeded : locks[k] = NONE \/ locks[k] = c
       IN canAcquire =>
          /\ locks' = [k \in Keys |-> IF k \in keysNeeded THEN c ELSE locks[k]]
          /\ txnState' = [txnState EXCEPT ![c] = "Locking"]
          /\ UNCHANGED <<kvStore, kvVersion, txnReadSet, txnWriteSet, txnReadValues, 
                        txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Complete locking phase for pessimistic client
CompleteLocking(c) ==
    /\ IsPessimistic(c)
    /\ txnState[c] = "Locking"
    /\ txnState' = [txnState EXCEPT ![c] = "Reading"]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Optimistic: Start reading immediately
StartOptimisticRead(c) ==
    /\ IsOptimistic(c)
    /\ txnState[c] = "Started"
    /\ txnState' = [txnState EXCEPT ![c] = "Reading"]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Read operation - sends request to primary
SendReadRequest(c, k) ==
    /\ txnState[c] = "Reading"
    /\ k \in txnReadSet[c]
    /\ txnReadValues[c][k] = NONE
    /\ messages' = messages \cup {[type |-> "ReadRequest", client |-> c, key |-> k, 
                                   primary |-> KeyToPrimary[k]]}
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet, 
                  txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount, commitLog, globalVersion>>

\* Primary responds to read request
ProcessReadRequest(msg) ==
    /\ msg \in messages
    /\ msg.type = "ReadRequest"
    /\ LET response == [type |-> "ReadResponse", client |-> msg.client, key |-> msg.key,
                       value |-> kvStore[msg.key], version |-> kvVersion[msg.key]]
       IN messages' = (messages \ {msg}) \cup {response}
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                  txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount, commitLog, globalVersion>>

\* Client receives read response
ReceiveReadResponse(c, msg) ==
    /\ msg \in messages
    /\ msg.type = "ReadResponse"
    /\ msg.client = c
    /\ txnState[c] = "Reading"
    /\ txnReadValues' = [txnReadValues EXCEPT ![c][msg.key] = msg.value]
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                  txnWriteValues, txnStartVersion, txnRetryCount, commitLog, globalVersion>>

\* Check if all reads are complete
AllReadsComplete(c) ==
    \A k \in txnReadSet[c] : txnReadValues[c][k] # NONE

\* Move to writing phase
StartWriting(c) ==
    /\ txnState[c] = "Reading"
    /\ AllReadsComplete(c)
    /\ txnState' = [txnState EXCEPT ![c] = "Writing"]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Compute write value based on read values (simple increment)
ComputeWriteValue(c, k) ==
    LET baseValue == IF k \in txnReadSet[c] THEN txnReadValues[c][k] ELSE kvStore[k]
    IN (baseValue + 1) % (MaxValue + 1)

\* Perform local write
PerformWrite(c, k) ==
    /\ txnState[c] = "Writing"
    /\ k \in txnWriteSet[c]
    /\ txnWriteValues[c][k] = NONE
    /\ txnWriteValues' = [txnWriteValues EXCEPT ![c][k] = ComputeWriteValue(c, k)]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                  txnReadValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Check if all writes are complete
AllWritesComplete(c) ==
    \A k \in txnWriteSet[c] : txnWriteValues[c][k] # NONE

\* Move to prepare phase
StartPrepare(c) ==
    /\ txnState[c] = "Writing"
    /\ AllWritesComplete(c)
    /\ txnState' = [txnState EXCEPT ![c] = "Preparing"]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Optimistic validation - check for conflicts
HasConflict(c) ==
    /\ IsOptimistic(c)
    /\ \E k \in (txnReadSet[c] \cup txnWriteSet[c]) :
        kvVersion[k] > txnStartVersion[c]

\* Check for write-write conflicts with other active transactions
HasWriteWriteConflict(c) ==
    \E other \in Clients :
        /\ other # c
        /\ txnState[other] \in {"Writing", "Preparing"}
        /\ (txnWriteSet[c] \cap txnWriteSet[other]) # {}

\* Pessimistic commit - apply writes atomically
PessimisticCommit(c) ==
    /\ IsPessimistic(c)
    /\ txnState[c] = "Preparing"
    /\ ~HasWriteWriteConflict(c)
    /\ kvStore' = [k \in Keys |-> IF k \in txnWriteSet[c] THEN txnWriteValues[c][k] ELSE kvStore[k]]
    /\ kvVersion' = [k \in Keys |-> IF k \in txnWriteSet[c] THEN globalVersion + 1 ELSE kvVersion[k]]
    /\ globalVersion' = globalVersion + 1
    /\ locks' = [k \in Keys |-> IF locks[k] = c THEN NONE ELSE locks[k]]
    /\ txnState' = [txnState EXCEPT ![c] = "Committed"]
    /\ commitLog' = Append(commitLog, [client |-> c, writeSet |-> txnWriteSet[c], 
                                       writes |-> txnWriteValues[c], version |-> globalVersion + 1])
    /\ UNCHANGED <<txnReadSet, txnWriteSet, txnReadValues, txnWriteValues, txnStartVersion, 
                  txnRetryCount, messages>>

\* Optimistic commit - validate and apply
OptimisticCommit(c) ==
    /\ IsOptimistic(c)
    /\ txnState[c] = "Preparing"
    /\ ~HasConflict(c)
    /\ ~HasWriteWriteConflict(c)
    /\ kvStore' = [k \in Keys |-> IF k \in txnWriteSet[c] THEN txnWriteValues[c][k] ELSE kvStore[k]]
    /\ kvVersion' = [k \in Keys |-> IF k \in txnWriteSet[c] THEN globalVersion + 1 ELSE kvVersion[k]]
    /\ globalVersion' = globalVersion + 1
    /\ txnState' = [txnState EXCEPT ![c] = "Committed"]
    /\ commitLog' = Append(commitLog, [client |-> c, writeSet |-> txnWriteSet[c],
                                       writes |-> txnWriteValues[c], version |-> globalVersion + 1])
    /\ UNCHANGED <<locks, txnReadSet, txnWriteSet, txnReadValues, txnWriteValues, 
                  txnStartVersion, txnRetryCount, messages>>

\* Optimistic abort due to conflict
OptimisticAbort(c) ==
    /\ IsOptimistic(c)
    /\ txnState[c] = "Preparing"
    /\ (HasConflict(c) \/ HasWriteWriteConflict(c))
    /\ txnState' = [txnState EXCEPT ![c] = "Aborted"]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Pessimistic abort (e.g., due to deadlock detection)
PessimisticAbort(c) ==
    /\ IsPessimistic(c)
    /\ txnState[c] \in {"Started", "Locking", "Reading", "Writing", "Preparing"}
    /\ HasWriteWriteConflict(c)
    /\ locks' = [k \in Keys |-> IF locks[k] = c THEN NONE ELSE locks[k]]
    /\ txnState' = [txnState EXCEPT ![c] = "Aborted"]
    /\ UNCHANGED <<kvStore, kvVersion, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, txnRetryCount, messages, commitLog, globalVersion>>

\* Retry aborted transaction (optimistic)
RetryTransaction(c) ==
    /\ txnState[c] = "Aborted"
    /\ txnRetryCount[c] < MaxRetries
    /\ txnState' = [txnState EXCEPT ![c] = "Idle"]
    /\ txnRetryCount' = [txnRetryCount EXCEPT ![c] = txnRetryCount[c] + 1]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, messages, commitLog, globalVersion>>

\* Reset committed transaction to idle
ResetTransaction(c) ==
    /\ txnState[c] \in {"Committed", "Aborted"}
    /\ txnState' = [txnState EXCEPT ![c] = "Idle"]
    /\ txnRetryCount' = [txnRetryCount EXCEPT ![c] = 0]
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnReadSet, txnWriteSet, txnReadValues,
                  txnWriteValues, txnStartVersion, messages, commitLog, globalVersion>>

\* Message loss (for modeling unreliable channels)
MessageLoss(msg) ==
    /\ msg \in messages
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                  txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount, commitLog, globalVersion>>

Next ==
    \/ \E c \in Clients : StartTransaction(c)
    \/ \E c \in Clients : AcquireLocks(c)
    \/ \E c \in Clients : CompleteLocking(c)
    \/ \E c \in Clients : StartOptimisticRead(c)
    \/ \E c \in Clients, k \in Keys : SendReadRequest(c, k)
    \/ \E msg \in messages : ProcessReadRequest(msg)
    \/ \E c \in Clients, msg \in messages : ReceiveReadResponse(c, msg)
    \/ \E c \in Clients : StartWriting(c)
    \/ \E c \in Clients, k \in Keys : PerformWrite(c, k)
    \/ \E c \in Clients : StartPrepare(c)
    \/ \E c \in Clients : PessimisticCommit(c)
    \/ \E c \in Clients : OptimisticCommit(c)
    \/ \E c \in Clients : OptimisticAbort(c)
    \/ \E c \in Clients : PessimisticAbort(c)
    \/ \E c \in Clients : RetryTransaction(c)
    \/ \E c \in Clients : ResetTransaction(c)

\* Fairness conditions
Fairness ==
    /\ \A c \in Clients : WF_<<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                            txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount,
                            messages, commitLog, globalVersion>>(StartTransaction(c))
    /\ \A c \in Clients : WF_<<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                            txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount,
                            messages, commitLog, globalVersion>>(PessimisticCommit(c))
    /\ \A c \in Clients : WF_<<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                            txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount,
                            messages, commitLog, globalVersion>>(OptimisticCommit(c))
    /\ \A c \in Clients : WF_<<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                            txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount,
                            messages, commitLog, globalVersion>>(RetryTransaction(c))

Spec == Init /\ [][Next]_<<kvStore, kvVersion, locks, txnState, txnReadSet, txnWriteSet,
                          txnReadValues, txnWriteValues, txnStartVersion, txnRetryCount,
                          messages, commitLog, globalVersion>> /\ Fairness

\* ============================================================================