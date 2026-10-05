---------------------------- MODULE DistributedTransaction ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Keys,           \* Set of all keys
    OptimisticClients,  \* Set of optimistic client IDs
    PessimisticClients, \* Set of pessimistic client IDs
    ReadKeys,       \* Function: client -> set of keys to read
    WriteKeys,      \* Function: client -> set of keys to write
    PrimaryKey      \* Function: client -> primary key

Clients == OptimisticClients \union PessimisticClients

VARIABLES
    \* Client state
    clientState,        \* Function: client -> state (idle, reading, locking, prewriting, committing, committed, aborted)
    clientStartTs,      \* Function: client -> start timestamp
    clientCommitTs,     \* Function: client -> commit timestamp (or 0 if not committed)
    clientReadData,     \* Function: client -> (key -> value read)
    clientLocksAcquired, \* Function: client -> set of keys locked
    clientPrewrites,    \* Function: client -> set of keys prewritten
    
    \* Key state (storage)
    keyData,            \* Function: key -> sequence of (value, writeTs, commitTs) records
    keyLock,            \* Function: key -> lock info {client, startTs} or NULL
    keyPrewrite,        \* Function: key -> prewrite info {client, startTs, value, primary} or NULL
    
    \* Global state
    globalTs,           \* Global timestamp counter
    
    \* Message state for tracking
    committedTxns,      \* Set of {client, startTs, commitTs, readKeys, writeKeys, readSnapshot}
    abortedTxns         \* Set of {client, startTs}

NULL == "NULL"

\* Type definitions
ClientStates == {"idle", "reading", "locking", "prewriting", "committing", "committed", "aborted"}

TypeOK ==
    /\ clientState \in [Clients -> ClientStates]
    /\ clientStartTs \in [Clients -> Nat]
    /\ clientCommitTs \in [Clients -> Nat]
    /\ clientReadData \in [Clients -> [Keys -> Nat]]
    /\ clientLocksAcquired \in [Clients -> SUBSET Keys]
    /\ clientPrewrites \in [Clients -> SUBSET Keys]
    /\ \A k \in Keys: keyLock[k] \in ({NULL} \union [client: Clients, startTs: Nat])
    /\ \A k \in Keys: keyPrewrite[k] \in ({NULL} \union [client: Clients, startTs: Nat, value: Nat, primary: Keys])
    /\ globalTs \in Nat

\* Helper: Get latest committed value for a key at a given timestamp
GetValueAtTs(key, ts) ==
    LET validRecords == {r \in keyData[key] : r.commitTs <= ts}
    IN IF validRecords = {} THEN 0
       ELSE LET maxTs == CHOOSE r \in validRecords : 
                            \A r2 \in validRecords : r.commitTs >= r2.commitTs
            IN maxTs.value

\* Helper: Check if key has pending prewrite
HasPendingPrewrite(key) == keyPrewrite[key] # NULL

\* Helper: Check if key is locked
IsLocked(key) == keyLock[key] # NULL

\* Helper: Check if key is locked by client
IsLockedBy(key, c) == 
    /\ keyLock[key] # NULL 
    /\ keyLock[key].client = c

\* Initialize state
Init ==
    /\ clientState = [c \in Clients |-> "idle"]
    /\ clientStartTs = [c \in Clients |-> 0]
    /\ clientCommitTs = [c \in Clients |-> 0]
    /\ clientReadData = [c \in Clients |-> [k \in Keys |-> 0]]
    /\ clientLocksAcquired = [c \in Clients |-> {}]
    /\ clientPrewrites = [c \in Clients |-> {}]
    /\ keyData = [k \in Keys |-> {}]
    /\ keyLock = [k \in Keys |-> NULL]
    /\ keyPrewrite = [k \in Keys |-> NULL]
    /\ globalTs = 1
    /\ committedTxns = {}
    /\ abortedTxns = {}

\* Optimistic client starts transaction and begins reading
OptimisticStart(c) ==
    /\ c \in OptimisticClients
    /\ clientState[c] = "idle"
    /\ clientState' = [clientState EXCEPT ![c] = "reading"]
    /\ clientStartTs' = [clientStartTs EXCEPT ![c] = globalTs]
    /\ globalTs' = globalTs + 1
    /\ UNCHANGED <<clientCommitTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, committedTxns, abortedTxns>>

\* Optimistic client reads a key
OptimisticRead(c, k) ==
    /\ c \in OptimisticClients
    /\ clientState[c] = "reading"
    /\ k \in ReadKeys[c]
    /\ clientReadData[c][k] = 0  \* Haven't read this key yet
    /\ ~HasPendingPrewrite(k)    \* No pending prewrite blocking
    /\ LET val == GetValueAtTs(k, clientStartTs[c])
       IN clientReadData' = [clientReadData EXCEPT ![c][k] = val + 1]  \* +1 to distinguish from unread
    /\ UNCHANGED <<clientState, clientStartTs, clientCommitTs, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, globalTs, committedTxns, abortedTxns>>

\* Optimistic client finished reading, move to prewriting
OptimisticFinishReading(c) ==
    /\ c \in OptimisticClients
    /\ clientState[c] = "reading"
    /\ \A k \in ReadKeys[c]: clientReadData[c][k] # 0  \* All reads done
    /\ clientState' = [clientState EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<clientStartTs, clientCommitTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, globalTs, committedTxns, abortedTxns>>

\* Pessimistic client starts transaction and begins locking
PessimisticStart(c) ==
    /\ c \in PessimisticClients
    /\ clientState[c] = "idle"
    /\ clientState' = [clientState EXCEPT ![c] = "locking"]
    /\ clientStartTs' = [clientStartTs EXCEPT ![c] = globalTs]
    /\ globalTs' = globalTs + 1
    /\ UNCHANGED <<clientCommitTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, committedTxns, abortedTxns>>

\* Pessimistic client acquires lock on a key
PessimisticLock(c, k) ==
    /\ c \in PessimisticClients
    /\ clientState[c] = "locking"
    /\ k \in (ReadKeys[c] \union WriteKeys[c])
    /\ k \notin clientLocksAcquired[c]
    /\ ~IsLocked(k)
    /\ ~HasPendingPrewrite(k)
    /\ keyLock' = [keyLock EXCEPT ![k] = [client |-> c, startTs |-> clientStartTs[c]]]
    /\ clientLocksAcquired' = [clientLocksAcquired EXCEPT ![c] = @ \union {k}]
    \* Pessimistic read happens at lock time
    /\ LET val == GetValueAtTs(k, clientStartTs[c])
       IN clientReadData' = [clientReadData EXCEPT ![c][k] = val + 1]
    /\ UNCHANGED <<clientState, clientStartTs, clientCommitTs, clientPrewrites,
                   keyData, keyPrewrite, globalTs, committedTxns, abortedTxns>>

\* Pessimistic client finished locking, move to prewriting
PessimisticFinishLocking(c) ==
    /\ c \in PessimisticClients
    /\ clientState[c] = "locking"
    /\ clientLocksAcquired[c] = (ReadKeys[c] \union WriteKeys[c])
    /\ clientState' = [clientState EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<clientStartTs, clientCommitTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, globalTs, committedTxns, abortedTxns>>

\* Client prewrites a key (both optimistic and pessimistic)
Prewrite(c, k) ==
    /\ clientState[c] = "prewriting"
    /\ k \in WriteKeys[c]
    /\ k \notin clientPrewrites[c]
    /\ \/ (c \in PessimisticClients /\ IsLockedBy(k, c))  \* Pessimistic: must hold lock
       \/ (c \in OptimisticClients /\ ~IsLocked(k) /\ ~HasPendingPrewrite(k))  \* Optimistic: no conflict
    /\ keyPrewrite' = [keyPrewrite EXCEPT ![k] = [client |-> c, 
                                                   startTs |-> clientStartTs[c],
                                                   value |-> clientStartTs[c],  \* Use startTs as written value
                                                   primary |-> PrimaryKey[c]]]
    /\ clientPrewrites' = [clientPrewrites EXCEPT ![c] = @ \union {k}]
    \* Release pessimistic lock when prewrite happens
    /\ keyLock' = [keyLock EXCEPT ![k] = NULL]
    /\ clientLocksAcquired' = [clientLocksAcquired EXCEPT ![c] = @ \ {k}]
    /\ UNCHANGED <<clientState, clientStartTs, clientCommitTs, clientReadData,
                   keyData, globalTs, committedTxns, abortedTxns>>

\* Client finished prewriting, move to committing
FinishPrewriting(c) ==
    /\ clientState[c] = "prewriting"
    /\ clientPrewrites[c] = WriteKeys[c]
    /\ clientState' = [clientState EXCEPT ![c] = "committing"]
    /\ clientCommitTs' = [clientCommitTs EXCEPT ![c] = globalTs]
    /\ globalTs' = globalTs + 1
    /\ UNCHANGED <<clientStartTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, committedTxns, abortedTxns>>

\* Commit primary key
CommitPrimary(c) ==
    /\ clientState[c] = "committing"
    /\ LET pk == PrimaryKey[c]
       IN /\ keyPrewrite[pk] # NULL
          /\ keyPrewrite[pk].client = c
          /\ keyData' = [keyData EXCEPT ![pk] = @ \union 
                         {[value |-> keyPrewrite[pk].value,
                           writeTs |-> clientStartTs[c],
                           commitTs |-> clientCommitTs[c]]}]
          /\ keyPrewrite' = [keyPrewrite EXCEPT ![pk] = NULL]
    /\ UNCHANGED <<clientState, clientStartTs, clientCommitTs, clientReadData, 
                   clientLocksAcquired, clientPrewrites,
                   keyLock, globalTs, committedTxns, abortedTxns>>

\* Commit secondary key
CommitSecondary(c, k) ==
    /\ clientState[c] = "committing"
    /\ k \in WriteKeys[c]
    /\ k # PrimaryKey[c]
    /\ keyPrewrite[k] # NULL
    /\ keyPrewrite[k].client = c
    \* Primary must be committed first
    /\ keyPrewrite[PrimaryKey[c]] = NULL
    /\ keyData' = [keyData EXCEPT ![k] = @ \union 
                   {[value |-> keyPrewrite[k].value,
                     writeTs |-> clientStartTs[c],
                     commitTs |-> clientCommitTs[c]]}]
    /\ keyPrewrite' = [keyPrewrite EXCEPT ![k] = NULL]
    /\ UNCHANGED <<clientState, clientStartTs, clientCommitTs, clientReadData,
                   clientLocksAcquired, clientPrewrites,
                   keyLock, globalTs, committedTxns, abortedTxns>>

\* Finish commit
FinishCommit(c) ==
    /\ clientState[c] = "committing"
    /\ \A k \in WriteKeys[c]: keyPrewrite[k] = NULL \/ keyPrewrite[k].client # c
    /\ clientState' = [clientState EXCEPT ![c] = "committed"]
    /\ committedTxns' = committedTxns \union 
                        {[client |-> c, 
                          startTs |-> clientStartTs[c],
                          commitTs |-> clientCommitTs[c],
                          readKeys |-> ReadKeys[c],
                          writeKeys |-> WriteKeys[c],
                          readSnapshot |-> clientReadData[c]]}
    /\ UNCHANGED <<clientStartTs, clientCommitTs, clientReadData, clientLocksAcquired, clientPrewrites,
                   keyData, keyLock, keyPrewrite, globalTs, abortedTxns>>

\* Abort transaction (can happen during various phases due to conflicts)
AbortTransaction(c) ==
    /\ clientState[c] \in {"reading", "locking", "prewriting", "committing"}
    /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
    \* Release all locks held by this client
    /\ keyLock' = [k \in Keys |-> IF keyLock[k] # NULL /\ keyLock[k].client = c 
                                  THEN NULL ELSE keyLock[k]]
    \* Remove all prewrites by this client
    /\ keyPrewrite' = [k \in Keys |-> IF keyPrewrite[k] # NULL /\ keyPrewrite[k].client = c
                                       THEN NULL ELSE keyPrewrite[k]]
    /\ clientLocksAcquired' = [clientLocksAcquired EXCEPT ![c] = {}]
    /\ clientPrewrites' = [clientPrewrites EXCEPT ![c] = {}]
    /\ abortedTxns' = abortedTxns \union {[client |-> c, startTs |-> clientStartTs[c]]}
    /\ UNCHANGED <<clientStartTs, clientCommitTs, clientReadData,
                   keyData, globalTs, committedTxns>>

\* Next state relation
Next ==
    \/ \E c \in OptimisticClients: OptimisticStart(c)
    \/ \E c \in OptimisticClients, k \in Keys: OptimisticRead(c, k)
    \/ \E c \in OptimisticClients: OptimisticFinishReading(c)
    \/ \E c \in PessimisticClients: PessimisticStart(c)
    \/ \E c \in PessimisticClients, k \in Keys: PessimisticLock(c, k)
    \/ \E c \in PessimisticClients: PessimisticFinishLocking(c)
    \/ \E c \in Clients, k \in Keys: Prewrite(c, k)
    \/ \E c \in Clients: FinishPrewriting(c)
    \/ \E c \in Clients: CommitPrimary(c)
    \/ \E c \in Clients, k \in Keys: CommitSecondary(c, k)
    \/ \E c \in Clients: FinishCommit(c)
    \/ \E c \in Clients: AbortTransaction(c)

\* Fairness conditions
Fairness ==
    /\ \A c \in OptimisticClients: WF_<<clientState, clientStartTs, clientCommitTs, clientReadData, 
                                       clientLocksAcquired, clientPrewrites, keyData, keyLock, 
                                       keyPrewrite, globalTs, committedTxns, abortedTxns>>(OptimisticStart(c))
    /\ \A c \in PessimisticClients: WF_<<clientState, clientStartTs, clientCommitTs, clientReadData,
                                         clientLocksAcquired, clientPrewrites, keyData, keyLock,
                                         keyPrewrite, globalTs, committedTxns, abortedTxns>>(PessimisticStart(c))

\* Specification
Spec == Init /\ [][Next]_<<clientState, clientStartTs, clientCommitTs, clientReadData, 
                           clientLocksAcquired, clientPrewrites, keyData, keyLock, 
                           keyPrewrite, globalTs, committedTxns, abortedTxns>>

FairSpec == Spec /\ Fairness

\* =============