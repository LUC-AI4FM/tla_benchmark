---------------------------- MODULE KVsnap ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Key, TxId, NoVal

\* Instantiating ClientCentric enables us to check transaction isolation
\* guarantees this model satisfies
CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}

\* Local helper operators
IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
Range(f) == {f[x] : x \in DOMAIN f}

\* For instantiating the ClientCentric module
wOp(k, v) == CC!w(k, v)
rOp(k, v) == CC!r(k, v)
InitialState == [k \in Key |-> NoVal]
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

(* --algorithm KVsnap {

variables
    \* A data store mapping keys to values
    store = [k \in Key |-> NoVal],

    \* The set of open snapshot transactions
    tx = {},

    \* The set of writes invisible to each transaction
    missed = [t \in TxId |-> {}],

    \* reads/writes per txn_id, used for interfacing to CC
    ops = [tId \in TxId |-> <<>>];

fair process (t \in TxId)
variables
    snapshotStore = [k \in Key |-> NoVal],
    read_keys = {},
    write_keys = {};
{
START:
    tx := tx \union {self};
    snapshotStore := store;
    with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
        read_keys := rk;
        write_keys := wk;
    };

READ:
    ops[self] := ops[self] \o SetToSeq({rOp(k, snapshotStore[k]) : k \in read_keys});

UPDATE:
    snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];

COMMIT:
    if (missed[self] \intersect write_keys = {}) {
        tx := tx \ {self};
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
        store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
        ops[self] := ops[self] \o SetToSeq({wOp(k, self) : k \in write_keys});
    }
}
}
*)
\* BEGIN TRANSLATION
VARIABLES store, tx, missed, ops, pc, snapshotStore, read_keys, write_keys

vars == << store, tx, missed, ops, pc, snapshotStore, read_keys, write_keys >>

ProcSet == (TxId)

Init == (* Global variables *)
        /\ store = [k \in Key |-> NoVal]
        /\ tx = {}
        /\ missed = [t \in TxId |-> {}]
        /\ ops = [tId \in TxId |-> <<>>]
        (* Process t *)
        /\ snapshotStore = [self \in TxId |-> [k \in Key |-> NoVal]]
        /\ read_keys = [self \in TxId |-> {}]
        /\ write_keys = [self \in TxId |-> {}]
        /\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
               /\ tx' = (tx \union {self})
               /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
               /\ \E rk \in SUBSET Key \ { {} }:
                    \E wk \in SUBSET Key \ { {} }:
                      /\ read_keys' = [read_keys EXCEPT ![self] = rk]
                      /\ write_keys' = [write_keys EXCEPT ![self] = wk]
               /\ pc' = [pc EXCEPT ![self] = "READ"]
               /\ UNCHANGED << store, missed, ops >>

READ(self) == /\ pc[self] = "READ"
              /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]) : k \in read_keys[self]})]
              /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
              /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, write_keys >>

UPDATE(self) == /\ pc[self] = "UPDATE"
                /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k]]]
                /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
                /\ UNCHANGED << store, tx, missed, ops, read_keys, write_keys >>

COMMIT(self) == /\ pc[self] = "COMMIT"
                /\ IF missed[self] \intersect write_keys[self] = {}
                      THEN /\ tx' = tx \ {self}
                           /\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
                           /\ store' = [k \in Key |-> IF k \in write_keys[self] THEN snapshotStore[self][k] ELSE store[k]]
                           /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self) : k \in write_keys[self]})]
                      ELSE /\ UNCHANGED << store, tx, missed, ops >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << snapshotStore, read_keys, write_keys >>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TxId : t(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TxId : WF_vars(t(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

TypeOK ==
    /\ store \in [Key -> TxId \union {NoVal}]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ pc \in [ProcSet -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]
    /\ snapshotStore \in [TxId -> [Key -> TxId \union {NoVal}]]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]

\* Snapshot isolation invariant
SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

\* Serializability would not be satisfied due to write-skew
Serialization == CC!Serializability(InitialState, Range(ops))

=============================================================================