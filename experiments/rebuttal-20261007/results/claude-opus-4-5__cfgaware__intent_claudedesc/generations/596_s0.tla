---------------------------- MODULE distributed_transaction ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Key,
    OptimisticClient,
    PessimisticClient,
    ClientKey,
    ClientPrimaryKey,
    ClientReadKey,
    ClientWriteKey

VARIABLES
    clientState,
    clientTS,
    clientReadSet,
    clientWriteSet,
    clientLockedKeys,
    keyLock,
    keyWrite,
    keyCommit,
    msgs,
    nextTS

vars == <<clientState, clientTS, clientReadSet, clientWriteSet, clientLockedKeys,
          keyLock, keyWrite, keyCommit, msgs, nextTS>>

Client == OptimisticClient \union PessimisticClient

TypeOK ==
    /\ clientState \in [Client -> {"init", "reading", "locking", "prewriting", "committing", "committed", "aborted"}]
    /\ clientTS \in [Client -> Nat]
    /\ clientReadSet \in [Client -> [Key -> Nat]]
    /\ clientWriteSet \in [Client -> SUBSET Key]
    /\ clientLockedKeys \in [Client -> SUBSET Key]
    /\ keyLock \in [Key -> [locked: BOOLEAN, holder: Client \union {CHOOSE x : x \notin Client}, ts: Nat]]
    /\ keyWrite \in [Key -> Seq([ts: Nat, value: Nat])]
    /\ keyCommit \in [Key -> SUBSET Nat]
    /\ msgs \in SUBSET [type: {"lock_req", "lock_resp", "prewrite_req", "prewrite_resp", 
                               "commit_req", "commit_resp", "read_req", "read_resp"},
                        client: Client, key: Key, ts: Nat, success: BOOLEAN, value: Nat]
    /\ nextTS \in Nat

NullClient == CHOOSE x : x \notin Client

Init ==
    /\ clientState = [c \in Client |-> "init"]
    /\ clientTS = [c \in Client |-> 0]
    /\ clientReadSet = [c \in Client |-> [k \in Key |-> 0]]
    /\ clientWriteSet = [c \in Client |-> {}]
    /\ clientLockedKeys = [c \in Client |-> {}]
    /\ keyLock = [k \in Key |-> [locked |-> FALSE, holder |-> NullClient, ts |-> 0]]
    /\ keyWrite = [k \in Key |-> <<>>]
    /\ keyCommit = [k \in Key |-> {0}]
    /\ msgs = {}
    /\ nextTS = 1

GetLatestCommittedValue(k, ts) ==
    LET committed == {w.ts : w \in {keyWrite[k][i] : i \in 1..Len(keyWrite[k])} 
                            \intersect {[ts |-> t, value |-> v] : t \in keyCommit[k], v \in Nat}}
        validTS == {t \in keyCommit[k] : t <= ts}
    IN IF validTS = {} THEN 0 ELSE CHOOSE t \in validTS : \A t2 \in validTS : t >= t2

StartOptimisticTransaction(c) ==
    /\ c \in OptimisticClient
    /\ clientState[c] = "init"
    /\ clientState' = [clientState EXCEPT ![c] = "reading"]
    /\ clientTS' = [clientTS EXCEPT ![c] = nextTS]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED <<clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs>>

StartPessimisticTransaction(c) ==
    /\ c \in PessimisticClient
    /\ clientState[c] = "init"
    /\ clientState' = [clientState EXCEPT ![c] = "locking"]
    /\ clientTS' = [clientTS EXCEPT ![c] = nextTS]
    /\ nextTS' = nextTS + 1
    /\ UNCHANGED <<clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs>>

OptimisticRead(c, k) ==
    /\ c \in OptimisticClient
    /\ clientState[c] = "reading"
    /\ k \in ClientReadKey[c]
    /\ clientReadSet[c][k] = 0
    /\ ~keyLock[k].locked \/ keyLock[k].ts > clientTS[c]
    /\ LET readTS == GetLatestCommittedValue(k, clientTS[c])
       IN clientReadSet' = [clientReadSet EXCEPT ![c][k] = IF readTS = 0 THEN clientTS[c] ELSE readTS]
    /\ UNCHANGED <<clientState, clientTS, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs, nextTS>>

FinishOptimisticReading(c) ==
    /\ c \in OptimisticClient
    /\ clientState[c] = "reading"
    /\ \A k \in ClientReadKey[c] : clientReadSet[c][k] # 0
    /\ clientState' = [clientState EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs, nextTS>>

PessimisticLock(c, k) ==
    /\ c \in PessimisticClient
    /\ clientState[c] = "locking"
    /\ k \in ClientKey[c]
    /\ k \notin clientLockedKeys[c]
    /\ ~keyLock[k].locked
    /\ keyLock' = [keyLock EXCEPT ![k] = [locked |-> TRUE, holder |-> c, ts |-> clientTS[c]]]
    /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = @ \union {k}]
    /\ LET readTS == GetLatestCommittedValue(k, clientTS[c])
       IN clientReadSet' = [clientReadSet EXCEPT ![c][k] = IF readTS = 0 THEN clientTS[c] ELSE readTS]
    /\ UNCHANGED <<clientState, clientTS, clientWriteSet, keyWrite, keyCommit, msgs, nextTS>>

PessimisticLockFail(c, k) ==
    /\ c \in PessimisticClient
    /\ clientState[c] = "locking"
    /\ k \in ClientKey[c]
    /\ k \notin clientLockedKeys[c]
    /\ keyLock[k].locked
    /\ keyLock[k].holder # c
    /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
    /\ \A lockedK \in clientLockedKeys[c] : 
        keyLock' = [keyLock EXCEPT ![lockedK] = [locked |-> FALSE, holder |-> NullClient, ts |-> 0]]
    /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = {}]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, keyWrite, keyCommit, msgs, nextTS>>

FinishPessimisticLocking(c) ==
    /\ c \in PessimisticClient
    /\ clientState[c] = "locking"
    /\ ClientKey[c] \subseteq clientLockedKeys[c]
    /\ clientState' = [clientState EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs, nextTS>>

Prewrite(c, k) ==
    /\ clientState[c] = "prewriting"
    /\ k \in ClientWriteKey[c]
    /\ k \notin clientWriteSet[c]
    /\ \/ (c \in OptimisticClient /\ ~keyLock[k].locked)
       \/ (c \in PessimisticClient /\ keyLock[k].holder = c)
    /\ IF c \in OptimisticClient
       THEN keyLock' = [keyLock EXCEPT ![k] = [locked |-> TRUE, holder |-> c, ts |-> clientTS[c]]]
       ELSE UNCHANGED keyLock
    /\ keyWrite' = [keyWrite EXCEPT ![k] = Append(@, [ts |-> clientTS[c], value |-> clientTS[c]])]
    /\ clientWriteSet' = [clientWriteSet EXCEPT ![c] = @ \union {k}]
    /\ IF c \in OptimisticClient
       THEN clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = @ \union {k}]
       ELSE UNCHANGED clientLockedKeys
    /\ UNCHANGED <<clientState, clientTS, clientReadSet, keyCommit, msgs, nextTS>>

PrewriteFail(c, k) ==
    /\ c \in OptimisticClient
    /\ clientState[c] = "prewriting"
    /\ k \in ClientWriteKey[c]
    /\ k \notin clientWriteSet[c]
    /\ keyLock[k].locked
    /\ keyLock[k].holder # c
    /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
    /\ keyLock' = [key \in Key |-> 
        IF key \in clientLockedKeys[c] 
        THEN [locked |-> FALSE, holder |-> NullClient, ts |-> 0]
        ELSE keyLock[key]]
    /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = {}]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, keyWrite, keyCommit, msgs, nextTS>>

FinishPrewriting(c) ==
    /\ clientState[c] = "prewriting"
    /\ ClientWriteKey[c] \subseteq clientWriteSet[c]
    /\ clientState' = [clientState EXCEPT ![c] = "committing"]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs, nextTS>>

CommitPrimary(c) ==
    /\ clientState[c] = "committing"
    /\ LET pk == ClientPrimaryKey[c]
       IN /\ keyLock[pk].locked
          /\ keyLock[pk].holder = c
          /\ keyCommit' = [keyCommit EXCEPT ![pk] = @ \union {clientTS[c]}]
          /\ keyLock' = [keyLock EXCEPT ![pk] = [locked |-> FALSE, holder |-> NullClient, ts |-> 0]]
          /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = @ \ {pk}]
    /\ UNCHANGED <<clientState, clientTS, clientReadSet, clientWriteSet, keyWrite, msgs, nextTS>>

CommitSecondary(c, k) ==
    /\ clientState[c] = "committing"
    /\ k \in ClientWriteKey[c]
    /\ k # ClientPrimaryKey[c]
    /\ clientTS[c] \in keyCommit[ClientPrimaryKey[c]]
    /\ k \in clientLockedKeys[c]
    /\ keyLock[k].locked
    /\ keyLock[k].holder = c
    /\ keyCommit' = [keyCommit EXCEPT ![k] = @ \union {clientTS[c]}]
    /\ keyLock' = [keyLock EXCEPT ![k] = [locked |-> FALSE, holder |-> NullClient, ts |-> 0]]
    /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = @ \ {k}]
    /\ UNCHANGED <<clientState, clientTS, clientReadSet, clientWriteSet, keyWrite, msgs, nextTS>>

FinishCommit(c) ==
    /\ clientState[c] = "committing"
    /\ clientLockedKeys[c] = {}
    /\ \A k \in ClientWriteKey[c] : clientTS[c] \in keyCommit[k]
    /\ clientState' = [clientState EXCEPT ![c] = "committed"]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, clientLockedKeys, keyLock, keyWrite, keyCommit, msgs, nextTS>>

Abort(c) ==
    /\ clientState[c] \in {"reading", "locking", "prewriting"}
    /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
    /\ keyLock' = [k \in Key |->
        IF k \in clientLockedKeys[c]
        THEN [locked |-> FALSE, holder |-> NullClient, ts |-> 0]
        ELSE keyLock[k]]
    /\ clientLockedKeys' = [clientLockedKeys EXCEPT ![c] = {}]
    /\ UNCHANGED <<clientTS, clientReadSet, clientWriteSet, keyWrite, keyCommit, msgs, nextTS>>

Next ==
    \/ \E c \in OptimisticClient : StartOptimisticTransaction(c)
    \/ \E c \in PessimisticClient : StartPessimisticTransaction(c)
    \/ \E c \in OptimisticClient, k \in Key : OptimisticRead(c, k)
    \/ \E c \in OptimisticClient : FinishOptimisticReading(c)
    \/ \E c \in PessimisticClient, k \in Key : PessimisticLock(c, k)
    \/ \E c \in PessimisticClient, k \in Key : PessimisticLockFail(c, k)
    \/ \E c \in PessimisticClient : FinishPessimisticLocking(c)
    \/ \E c \in Client, k \in Key : Prewrite(c, k)
    \/ \E c \in Client, k \in Key : PrewriteFail(c, k)
    \/ \E c \in Client : FinishPrewriting(c)
    \/ \E c \in Client : CommitPrimary(c)
    \/ \E c \in Client, k \in Key : CommitSecondary(c, k)
    \/ \E c \in Client : FinishCommit(c)
    \/ \E c \in Client : Abort(c)

Spec == Init /\ [][Next]_vars

UniqueCommitAbort ==
    \A c \in Client : ~(clientState[c] = "committed" /\ clientState[c] = "aborted")

CommittedSnapshotConsistency ==
    \A c \in Client : clientState[c] = "committed" =>
        \A k \in ClientWriteKey[c] : clientTS[c] \in keyCommit[k]

AbortedConsistency ==
    \A c \in Client : clientState[c] = "aborted" =>
        clientLockedKeys[c] = {}

NoWriteConflict ==
    \A k \in Key : \A i, j \in 1..Len(keyWrite[k]) :
        i # j => keyWrite[k][i].ts # keyWrite[k][j].ts \/ 
                 ~(keyWrite[k][i].ts \in keyCommit[k] /\ keyWrite[k][j].ts \in keyCommit[k])

NoDuplicateLocks ==
    \A k \in Key : Cardinality({c \in Client : keyLock[k].holder = c /\ keyLock[k].locked}) <= 1

NoDuplicateWrites ==
    \A c \in Client, k \in Key : 
        clientState[c] \in {"prewriting", "committing", "committed"} =>
            Cardinality({i \in 1..Len(keyWrite[k]) : keyWrite[k][i].ts = clientTS[c]}) <= 1

SingleWritePerCommittedTransaction ==
    \A c \in Client : clientState[c] = "committed" =>
        \A k \in ClientWriteKey[c] :
            Cardinality({i \in 1..Len(keyWrite[k]) : keyWrite[k][i].ts = clientTS[c] /\ clientTS[c] \in keyCommit[k]}) = 1

OptimisticSnapshotIsolation ==
    \A c \in OptimisticClient : clientState[c] \in {"prewriting", "committing", "committed"} =>
        \A k \in ClientReadKey[c] : clientReadSet[c][k] <= clientTS[c]

PessimisticSnapshotIsolation ==
    \A c \in PessimisticClient : clientState[c] \in {"prewriting", "committing", "committed"} =>
        \A k \in ClientReadKey[c] : clientReadSet[c][k] <= clientTS[c]

TimestampConsistency ==
    \A c \in Client : clientTS[c] < nextTS

Safety ==
    /\ TypeOK
    /\ UniqueCommitAbort
    /\ CommittedSnapshotConsistency
    /\ AbortedConsistency
    /\ NoWriteConflict
    /\ NoDuplicateLocks
    /\ NoDuplicateWrites
    /\ SingleWritePerCommittedTransaction
    /\ OptimisticSnapshotIsolation
    /\ PessimisticSnapshotIsolation
    /\ TimestampConsistency

=============================================================================