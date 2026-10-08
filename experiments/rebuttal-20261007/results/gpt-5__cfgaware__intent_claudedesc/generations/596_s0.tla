----------------------------- MODULE TxnSI -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
Distributed transaction system with optimistic and pessimistic clients
over a shared set of keys. Concrete scenario: 2 keys, 2 clients where
C1 is optimistic and C2 is pessimistic. Both read and write both keys.
*)

CONSTANTS

(*
Concrete scenario (fixed values as definitions).
*)
Keys == {"K1", "K2"}
Clients == {"C1", "C2"}
Optimistic == {"C1"}
Pessimistic == Clients \ Optimistic

Reads == [c \in Clients |-> Keys]
Writes == [c \in Clients |-> Keys]
Primary == [c \in Clients |-> IF c = "C1" THEN "K1" ELSE "K2"]

(*
Values written by each client to each key (deterministic for validation).
*)
NewVal(c, k) ==
  IF c = "C1" THEN (IF k = "K1" THEN 11 ELSE 12)
  ELSE (IF k = "K1" THEN 21 ELSE 22)

(*
Basic types and records
*)
NoneClient == "None"
NoKey == "NoKey"

Version == [val: Nat, ts: Nat, writer: Clients \cup {NoneClient}]
MsgType == {"ReadResp", "Lock", "Commit", "Abort"}
Msg == [type: MsgType, c: Clients, k: Keys \cup {NoKey}, ts: Nat, val: Nat]

(*
State variables
*)
VARIABLES
  kvHist,      \* [Keys -> Seq(Version)] version history per key
  curTs,       \* Nat, global logical time (monotonic increasing on commit)
  lockOwner,   \* [Keys -> SUBSET Clients], at most one holder per key
  pc,          \* [Clients -> {"Start","Lock","Read","Validate","Write","Commit","Abort","Done"}]
  snapTs,      \* [Clients -> Nat] snapshot timestamp chosen at tx begin
  readLog,     \* [Clients -> [Keys -> [present: BOOLEAN, val: Nat, ts: Nat]]]
  locksHeld,   \* [Clients -> SUBSET Keys]
  commitTs,    \* [Clients -> Nat] 0 if not committed, else unique > 0
  outcome,     \* [Clients -> {"None","Committed","Aborted"}] one-shot outcome
  msgs         \* Seq(Msg) message/event log with timestamps

vars == << kvHist, curTs, lockOwner, pc, snapTs, readLog, locksHeld, commitTs, outcome, msgs >>

(*
Helpers
*)
LastVersion(k) == kvHist[k][Len(kvHist[k])]
AllRead(c) == \A k \in Reads[c]: readLog[c][k].present
LockSet(c) == IF c \in Optimistic THEN Writes[c] ELSE Reads[c] \cup Writes[c]
AllLocked(c) == \A k \in LockSet(c): lockOwner[k] = {c}
Wrote(c, k) == \E i \in 1..Len(kvHist[k]): kvHist[k][i].writer = c

(*
Find the index of the latest version with ts <= t for a given sequence s of Versions.
Guaranteed to exist because genesis version has ts = 0 and t \in Nat.
*)
MaxLEIndexOfSeq(s, t) ==
  CHOOSE i \in { j \in 1..Len(s) : s[j].ts <= t /\ 
                                  \A q \in 1..Len(s) : s[q].ts <= t => s[j].ts >= s[q].ts } : TRUE

ReadAt(k, t) == kvHist[k][MaxLEIndexOfSeq(kvHist[k], t)]

(*
Type safety
*)
TypeOK ==
  /\ kvHist \in [Keys -> Seq(Version)]
  /\ \A k \in Keys: Len(kvHist[k]) >= 1 /\ kvHist[k][1].ts = 0 /\ kvHist[k][1].writer = NoneClient
  /\ curTs \in Nat
  /\ lockOwner \in [Keys -> SUBSET Clients]
  /\ \A k \in Keys: Cardinality(lockOwner[k]) <= 1
  /\ pc \in [Clients -> {"Start","Lock","Read","Validate","Write","Commit","Abort","Done"}]
  /\ snapTs \in [Clients -> Nat]
  /\ readLog \in [Clients -> [Keys -> [present: BOOLEAN, val: Nat, ts: Nat]]]
  /\ locksHeld \in [Clients -> SUBSET Keys]
  /\ commitTs \in [Clients -> Nat]
  /\ outcome \in [Clients -> {"None","Committed","Aborted"}]
  /\ msgs \in Seq(Msg)

(*
Initial state
*)
Init ==
  /\ kvHist = [k \in Keys |-> << [val |-> 0, ts |-> 0, writer |-> NoneClient] >>]
  /\ curTs = 0
  /\ lockOwner = [k \in Keys |-> {}]
  /\ pc = [c \in Clients |-> "Start"]
  /\ snapTs = [c \in Clients |-> 0]
  /\ readLog = [c \in Clients |-> [k \in Keys |-> [present |-> FALSE, val |-> 0, ts |-> 0]]]
  /\ locksHeld = [c \in Clients |-> {}]
  /\ commitTs = [c \in Clients |-> 0]
  /\ outcome = [c \in Clients |-> "None"]
  /\ msgs = << >>

(*
Actions
*)
DoBegin(c) ==
  /\ pc[c] = "Start"
  /\ LET nextPc == IF c \in Optimistic THEN "Read" ELSE "Lock" IN
     /\ pc' = [pc EXCEPT ![c] = nextPc]
     /\ snapTs' = [snapTs EXCEPT ![c] = curTs]
  /\ UNCHANGED << kvHist, curTs, lockOwner, readLog, locksHeld, commitTs, outcome, msgs >>

ReadStep(c) ==
  /\ pc[c] = "Read"
  /\ \E k \in Reads[c]:
       /\ ~ readLog[c][k].present
       /\ LET r == ReadAt(k, snapTs[c]) IN
            /\ readLog' = [readLog EXCEPT ![c][k] = [present |-> TRUE, val |-> r.val, ts |-> r.ts]]
            /\ msgs' = Append(msgs, [type |-> "ReadResp", c |-> c, k |-> k, ts |-> r.ts, val |-> r.val])
            /\ pc' = [pc EXCEPT ![c] = IF AllRead([readLog EXCEPT ![c][k] = [present |-> TRUE, val |-> r.val, ts |-> r.ts]][c])
                                      THEN (IF c \in Optimistic THEN "Lock" ELSE "Write")
                                      ELSE "Read"]
  /\ UNCHANGED << kvHist, curTs, lockOwner, snapTs, locksHeld, commitTs, outcome >>
  \* For pessimistic clients, ReadStep is only reachable after they have locked; the pc logic sets them to "Write" after all reads.

LockStep(c) ==
  /\ pc[c] = "Lock"
  /\ \E k \in LockSet(c) \ locksHeld[c]:
       /\ lockOwner[k] = {}
       /\ lockOwner' = [lockOwner EXCEPT ![k] = {c}]
       /\ locksHeld' = [locksHeld EXCEPT ![c] = @ \cup {k}]
       /\ msgs' = Append(msgs, [type |-> "Lock", c |-> c, k |-> k, ts |-> curTs, val |-> 0])
       /\ pc' = [pc EXCEPT ![c] =
                   IF \A kk \in LockSet(c): IF kk = k THEN {c} = lockOwner'[kk] ELSE {c} = lockOwner[kk]
                   THEN (IF c \in Optimistic THEN "Validate" ELSE "Read")
                   ELSE "Lock"]
  /\ UNCHANGED << kvHist, curTs, snapTs, readLog, commitTs, outcome >>

ValidOpt(c) ==
  /\ \A k \in Writes[c]: LastVersion(k).ts <= snapTs[c]
  /\ \A k \in Reads[c]: readLog[c][k].present /\ readLog[c][k].ts = ReadAt(k, snapTs[c]).ts

ValidatePass(c) ==
  /\ pc[c] = "Validate"
  /\ c \in Optimistic
  /\ ValidOpt(c)
  /\ pc' = [pc EXCEPT ![c] = "Write"]
  /\ UNCHANGED << kvHist, curTs, lockOwner, snapTs, readLog, locksHeld, commitTs, outcome, msgs >>

ValidateFail(c) ==
  /\ pc[c] = "Validate"
  /\ c \in Optimistic
  /\ ~ValidOpt(c)
  /\ pc' = [pc EXCEPT ![c] = "Abort"]
  /\ UNCHANGED << kvHist, curTs, lockOwner, snapTs, readLog, locksHeld, commitTs, outcome, msgs >>

WriteStep(c) ==
  /\ pc[c] = "Write"
  /\ \A k \in Writes[c]: lockOwner[k] = {c}
  /\ LET t == curTs + 1 IN
       /\ kvHist' = [k \in Keys |-> IF k \in Writes[c]
                                    THEN Append(kvHist[k], [val |-> NewVal(c,k), ts |-> t, writer |-> c])
                                    ELSE kvHist[k]]
       /\ curTs' = t
       /\ commitTs' = [commitTs EXCEPT ![c] = t]
       /\ pc' = [pc EXCEPT ![c] = "Commit"]
       /\ msgs' = Append(msgs, [type |-> "Commit", c |-> c, k |-> NoKey, ts |-> t, val |-> 0])
  /\ UNCHANGED << lockOwner, snapTs, readLog, locksHeld, outcome >>

FinishCommit(c) ==
  /\ pc[c] = "Commit"
  /\ lockOwner' = [k \in Keys |-> IF k \in locksHeld[c] THEN {} ELSE lockOwner[k]]
  /\ locksHeld' = [locksHeld EXCEPT ![c] = {}]
  /\ pc' = [pc EXCEPT ![c] = "Done"]
  /\ outcome' = [outcome EXCEPT ![c] = "Committed"]
  /\ UNCHANGED << kvHist, curTs, snapTs, readLog, commitTs, msgs >>

AbortStep(c) ==
  /\ pc[c] = "Abort"
  /\ lockOwner' = [k \in Keys |-> IF k \in locksHeld[c] THEN {} ELSE lockOwner[k]]
  /\ locksHeld' = [locksHeld EXCEPT ![c] = {}]
  /\ pc' = [pc EXCEPT ![c] = "Done"]
  /\ outcome' = [outcome EXCEPT ![c] = "Aborted"]
  /\ msgs' = Append(msgs, [type |-> "Abort", c |-> c, k |-> NoKey, ts |-> curTs, val |-> 0])
  /\ UNCHANGED << kvHist, curTs, snapTs, readLog, commitTs >>

Next ==
  \E c \in Clients:
    DoBegin(c)
    \/ ReadStep(c)
    \/ LockStep(c)
    \/ ValidatePass(c)
    \/ ValidateFail(c)
    \/ WriteStep(c)
    \/ FinishCommit(c)
    \/ AbortStep(c)

Spec == Init /\ [][Next]_vars

(*
Correctness properties and invariants
*)

Inv_UniqueOutcome ==
  /\ \A c \in Clients:
       /\ outcome[c] \in {"None","Committed","Aborted"}
       /\ (outcome[c] = "Committed") => commitTs[c] > 0
       /\ (outcome[c] = "Aborted") => commitTs[c] = 0

Inv_NoDoubleWritesPerTxn ==
  \A c \in Clients: \A k \in Keys:
    Cardinality({ i \in 1..Len(kvHist[k]) : kvHist[k][i].writer = c }) <= 1

Inv_CommittedTsUnique ==
  \A c, d \in Clients:
    c # d => ~(commitTs[c] > 0 /\ commitTs[d] > 0 /\ commitTs[c] = commitTs[d])

Inv_LockExclusivity ==
  /\ \A k \in Keys: Cardinality(lockOwner[k]) <= 1
  /\ \A c \in Clients: \A k \in locksHeld[c]: lockOwner[k] = {c}

Inv_ReadSnapshot ==
  \A c \in Clients: \A k \in Keys:
    readLog[c][k].present => readLog[c][k].ts = ReadAt(k, snapTs[c]).ts

Inv_OptValidateOnCommit ==
  \A c \in Clients:
    (outcome[c] = "Committed") =>
      /\ \A k \in Reads[c]: readLog[c][k].present /\ readLog[c][k].ts = ReadAt(k, snapTs[c]).ts
      /\ \A k \in Writes[c]:
           \A i \in 1..Len(kvHist[k]):
             (kvHist[k][i].ts > snapTs[c] /\ kvHist[k][i].ts < commitTs[c]) => FALSE

Inv_AbortNoWrites ==
  \A c \in Clients:
    (outcome[c] = "Aborted") =>
      \A k \in Keys: ~Wrote(c, k)

Inv_MsgTsMonotonic ==
  \A i, j \in 1..Len(msgs): i < j => msgs[i].ts <= msgs[j].ts

MsgConsistent(m) ==
  IF m.type = "ReadResp" THEN m.ts = ReadAt(m.k, snapTs[m.c]).ts
  ELSE IF m.type = "Commit" THEN m.ts = commitTs[m.c]
  ELSE TRUE

Inv_MsgConsistency ==
  \A i \in 1..Len(msgs): MsgConsistent(msgs[i])

Invariants ==
  /\ TypeOK
  /\ Inv_UniqueOutcome
  /\ Inv_NoDoubleWritesPerTxn
  /\ Inv_CommittedTsUnique
  /\ Inv_LockExclusivity
  /\ Inv_ReadSnapshot
  /\ Inv_OptValidateOnCommit
  /\ Inv_AbortNoWrites
  /\ Inv_MsgTsMonotonic
  /\ Inv_MsgConsistency

=============================================================================