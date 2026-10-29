---- MODULE MCKVsnap ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Key, TxId, NoVal

VARIABLES store, pc, snapshot, readKeys, writeKeys, startTs, commitTs, missed, clock

vars == <<store, pc, snapshot, readKeys, writeKeys, startTs, commitTs, missed, clock>>

Val == TxId \cup {NoVal}

TxIdSymmetric == Permutations(TxId)

TypeOK ==
    /\ store \in [Key -> Val]
    /\ pc \in [TxId -> {"init", "running", "committed", "aborted"}]
    /\ snapshot \in [TxId -> [Key -> Val]]
    /\ readKeys \in [TxId -> SUBSET Key]
    /\ writeKeys \in [TxId -> SUBSET Key]
    /\ startTs \in [TxId -> Nat]
    /\ commitTs \in [TxId -> Nat]
    /\ missed \in [TxId -> SUBSET Key]
    /\ clock \in Nat

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ pc = [t \in TxId |-> "init"]
    /\ snapshot = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ readKeys = [t \in TxId |-> {}]
    /\ writeKeys = [t \in TxId |-> {}]
    /\ startTs = [t \in TxId |-> 0]
    /\ commitTs = [t \in TxId |-> 0]
    /\ missed = [t \in TxId |-> {}]
    /\ clock = 1

\* A transaction starts: takes a snapshot of the store and picks read/write sets
Start(t) ==
    /\ pc[t] = "init"
    /\ \E rk \in (SUBSET Key) \ {{}}, wk \in (SUBSET Key) \ {{}} :
        /\ readKeys' = [readKeys EXCEPT ![t] = rk]
        /\ writeKeys' = [writeKeys EXCEPT ![t] = wk]
    /\ snapshot' = [snapshot EXCEPT ![t] = store]
    /\ startTs' = [startTs EXCEPT ![t] = clock]
    /\ clock' = clock + 1
    /\ pc' = [pc EXCEPT ![t] = "running"]
    /\ UNCHANGED <<store, commitTs, missed>>

\* Commit succeeds only if no concurrent committed tx wrote an overlapping key
Commit(t) ==
    /\ pc[t] = "running"
    /\ missed[t] \cap writeKeys[t] = {}
    /\ store' = [k \in Key |-> IF k \in writeKeys[t] THEN t ELSE store[k]]
    /\ missed' = [o \in TxId |->
                    IF o # t /\ pc[o] = "running"
                    THEN missed[o] \cup writeKeys[t]
                    ELSE missed[o]]
    /\ commitTs' = [commitTs EXCEPT ![t] = clock]
    /\ clock' = clock + 1
    /\ pc' = [pc EXCEPT ![t] = "committed"]
    /\ UNCHANGED <<snapshot, readKeys, writeKeys, startTs>>

Abort(t) ==
    /\ pc[t] = "running"
    /\ missed[t] \cap writeKeys[t] # {}
    /\ pc' = [pc EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<store, snapshot, readKeys, writeKeys, startTs, commitTs, missed, clock>>

Done == \A t \in TxId : pc[t] \in {"committed", "aborted"}

Terminating == Done /\ UNCHANGED vars

Next ==
    \/ \E t \in TxId : Start(t) \/ Commit(t) \/ Abort(t)
    \/ Terminating

Spec == Init /\ [][Next]_vars
        /\ \A t \in TxId : WF_vars(Start(t) \/ Commit(t) \/ Abort(t))

Committed == {t \in TxId : pc[t] = "committed"}

\* Committed writers of key k that committed before timestamp ts
WritersBefore(k, ts) == {u \in Committed : k \in writeKeys[u] /\ commitTs[u] < ts}

SnapshotReadsOK ==
    \A t \in Committed : \A k \in readKeys[t] :
        LET W == WritersBefore(k, startTs[t]) IN
            IF W = {}
            THEN snapshot[t][k] = NoVal
            ELSE /\ snapshot[t][k] \in W
                 /\ \A w \in W : commitTs[w] <= commitTs[snapshot[t][k]]

NoWriteWriteConflict ==
    \A t, u \in Committed :
        (t # u /\ writeKeys[t] \cap writeKeys[u] # {})
            => (commitTs[t] < startTs[u] \/ commitTs[u] < startTs[t])

SnapshotIsolation == SnapshotReadsOK /\ NoWriteWriteConflict

Termination == <>Done

\* Debugging aid: fails when distinct keys hold distinct non-null values after some depth
BaitInv ==
    TLCGet("level") < 8
    \/ ~(\E k1, k2 \in Key :
            /\ k1 # k2
            /\ store[k1] # NoVal
            /\ store[k2] # NoVal
            /\ store[k1] # store[k2])

====