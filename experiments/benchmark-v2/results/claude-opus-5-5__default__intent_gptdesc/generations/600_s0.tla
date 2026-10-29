------------------------- MODULE OptimisticTimestampKV -------------------------
(***************************************************************************)
(* A concurrent transactional key-value store with optimistic concurrency  *)
(* control and timestamp-ordered commits.                                  *)
(*                                                                         *)
(*  - A fixed set of Keys and a fixed set of symmetric Clients.            *)
(*  - Each client runs one transaction at a time, made of a read set and a *)
(*    write set. Several clients may target the same keys.                 *)
(*  - Execution is nonblocking. Reads observe the committed version of a   *)
(*    key and record its version number (the commit timestamp of the       *)
(*    writer).                                                             *)
(*  - Commit protocol, made of transient states so that races between      *)
(*    concurrent committers are possible:                                  *)
(*      active --StartCommit--> validating                                 *)
(*      validating --ValidateSuccess--> committing                         *)
(*          (assigns a unique commit timestamp and installs write intents) *)
(*      validating --ValidateFail--> aborted --Retry--> active             *)
(*      committing --Install--> committed                                  *)
(*          (writes become visible atomically and intents are released)    *)
(*  - Validation is the deterministic conflict-resolution point. A         *)
(*    transaction passes only if:                                          *)
(*      (a) every version it read is still current and not under an       *)
(*          intent, and                                                    *)
(*      (b) none of its write keys is under another transaction's intent.  *)
(*    So at most one of a set of conflicting writers is accepted.          *)
(*                                                                         *)
(* Model checking notes:                                                   *)
(*  - The global timestamp clock is bounded by MaxTS. Once it is           *)
(*    exhausted the system may halt, so disable deadlock checking.         *)
(*  - Symmetry (Perms) is sound for the invariants. Do not use it when     *)
(*    checking the liveness properties.                                    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys,      \* fixed set of keys
          Clients,   \* fixed set of (symmetric) clients
          MaxTS,     \* bound on commit timestamps (for finite model checking)
          NoClient   \* model value: "no client"

ASSUME /\ Keys # {}
       /\ Clients # {}
       /\ MaxTS \in Nat
       /\ NoClient \notin Clients

NoRead == -1                       \* marker: key not (yet) read
Versions == 0..MaxTS               \* version 0 = initial value
States == {"idle", "active", "validating", "committing", "committed", "aborted"}

VARIABLES
  store,     \* store[k] = [ver |-> commit ts of last writer, writer |-> client]
  intent,    \* intent[k] = client holding a write intent on k, or NoClient
  clock,     \* global timestamp oracle (last issued commit timestamp)
  cstate,    \* cstate[c] = state of client c's current transaction
  rset,      \* rset[c] = read set of c's transaction
  wset,      \* wset[c] = write set of c's transaction
  readVer,   \* readVer[c][k] = version observed by c's read of k, or NoRead
  commitTS,  \* commitTS[c] = commit timestamp assigned to c (0 if none)
  log        \* history of committed transactions (for verification)

vars == <<store, intent, clock, cstate, rset, wset, readVer, commitTS, log>>

LogEntry == [client : Clients,
             ts     : 1..MaxTS,
             reads  : [Keys -> {NoRead} \cup Versions],
             writes : SUBSET Keys]

TypeOK ==
  /\ store \in [Keys -> [ver : Versions, writer : Clients \cup {NoClient}]]
  /\ intent \in [Keys -> Clients \cup {NoClient}]
  /\ clock \in Versions
  /\ cstate \in [Clients -> States]
  /\ rset \in [Clients -> SUBSET Keys]
  /\ wset \in [Clients -> SUBSET Keys]
  /\ readVer \in [Clients -> [Keys -> {NoRead} \cup Versions]]
  /\ commitTS \in [Clients -> Versions]
  /\ log \subseteq LogEntry

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ store = [k \in Keys |-> [ver |-> 0, writer |-> NoClient]]
  /\ intent = [k \in Keys |-> NoClient]
  /\ clock = 0
  /\ cstate = [c \in Clients |-> "idle"]
  /\ rset = [c \in Clients |-> {}]
  /\ wset = [c \in Clients |-> {}]
  /\ readVer = [c \in Clients |-> [k \in Keys |-> NoRead]]
  /\ commitTS = [c \in Clients |-> 0]
  /\ log = {}

-----------------------------------------------------------------------------
(* Client actions *)

\* A client starts a new transaction with arbitrary read and write sets.
Begin(c) ==
  /\ cstate[c] \in {"idle", "committed"}
  /\ \E R, W \in SUBSET Keys :
       /\ R \cup W # {}
       /\ rset' = [rset EXCEPT ![c] = R]
       /\ wset' = [wset EXCEPT ![c] = W]
  /\ readVer' = [readVer EXCEPT ![c] = [k \in Keys |-> NoRead]]
  /\ commitTS' = [commitTS EXCEPT ![c] = 0]
  /\ cstate' = [cstate EXCEPT ![c] = "active"]
  /\ UNCHANGED <<store, intent, clock, log>>

\* Nonblocking read of the latest committed version of a key.
Read(c, k) ==
  /\ cstate[c] = "active"
  /\ k \in rset[c]
  /\ readVer[c][k] = NoRead
  /\ readVer' = [readVer EXCEPT ![c][k] = store[k].ver]
  /\ UNCHANGED <<store, intent, clock, cstate, rset, wset, commitTS, log>>

\* All reads are done (writes are buffered locally), so request commit.
StartCommit(c) ==
  /\ cstate[c] = "active"
  /\ \A k \in rset[c] : readVer[c][k] # NoRead
  /\ cstate' = [cstate EXCEPT ![c] = "validating"]
  /\ UNCHANGED <<store, intent, clock, rset, wset, readVer, commitTS, log>>

\* Optimistic validation condition.
CanCommit(c) ==
  /\ \A k \in rset[c] : /\ store[k].ver = readVer[c][k]
                        /\ intent[k] = NoClient
  /\ \A k \in wset[c] : intent[k] = NoClient

\* Validation succeeds: acquire a unique, monotonically increasing commit
\* timestamp and place write intents. This is the serialization point.
ValidateSuccess(c) ==
  /\ cstate[c] = "validating"
  /\ CanCommit(c)
  /\ clock < MaxTS
  /\ clock' = clock + 1
  /\ commitTS' = [commitTS EXCEPT ![c] = clock + 1]
  /\ intent' = [k \in Keys |-> IF k \in wset[c] THEN c ELSE intent[k]]
  /\ cstate' = [cstate EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<store, rset, wset, readVer, log>>

\* Validation fails because of a conflict: abort and make no writes.
ValidateFail(c) ==
  /\ cstate[c] = "validating"
  /\ ~CanCommit(c)
  /\ cstate' = [cstate EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<store, intent, clock, rset, wset, readVer, commitTS, log>>

\* Install all writes atomically with the commit timestamp as version,
\* then release the intents.
Install(c) ==
  /\ cstate[c] = "committing"
  /\ store' = [k \in Keys |->
                 IF k \in wset[c]
                   THEN [ver |-> commitTS[c], writer |-> c]
                   ELSE store[k]]
  /\ intent' = [k \in Keys |-> IF k \in wset[c] THEN NoClient ELSE intent[k]]
  /\ log' = log \cup {[client |-> c,
                       ts     |-> commitTS[c],
                       reads  |-> readVer[c],
                       writes |-> wset[c]]}
  /\ cstate' = [cstate EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<clock, rset, wset, readVer, commitTS>>

\* Retry an aborted transaction (same read and write sets, fresh reads).
Retry(c) ==
  /\ cstate[c] = "aborted"
  /\ readVer' = [readVer EXCEPT ![c] = [k \in Keys |-> NoRead]]
  /\ cstate' = [cstate EXCEPT ![c] = "active"]
  /\ UNCHANGED <<store, intent, clock, rset, wset, commitTS, log>>

-----------------------------------------------------------------------------
(* Specification *)

Validate(c) == ValidateSuccess(c) \/ ValidateFail(c)

Next ==
  \E c \in Clients :
     \/ Begin(c)
     \/ \E k \in Keys : Read(c, k)
     \/ StartCommit(c)
     \/ Validate(c)
     \/ Install(c)
     \/ Retry(c)

\* Weak fairness on every step of an in-progress transaction (not on Begin).
Fairness ==
  \A c \in Clients :
     /\ WF_vars(\E k \in Keys : Read(c, k))
     /\ WF_vars(StartCommit(c))
     /\ WF_vars(Validate(c))
     /\ WF_vars(Install(c))
     /\ WF_vars(Retry(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Helper operators *)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Commit timestamp of the latest committed write to k strictly before t
\* (0 = initial version).
LatestBefore(k, t) ==
  LET W == {e.ts : e \in {f \in log : k \in f.writes /\ f.ts < t}}
  IN  IF W = {} THEN 0 ELSE Max(W)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Commit timestamps are unique, so they define a total serial order.
UniqueCommitTS ==
  \A e1, e2 \in log : e1 # e2 => e1.ts # e2.ts

\* Serializability: running the committed transactions serially in commit
\* timestamp order, each read would return exactly the version it observed.
Serializability ==
  \A e \in log : \A k \in Keys :
     e.reads[k] # NoRead => e.reads[k] = LatestBefore(k, e.ts)

\* Atomicity: a committed transaction's writes are all reflected (possibly
\* overwritten later), and every visible version was produced by a committed
\* transaction that wrote that key. No partial or aborted writes are visible.
Atomicity ==
  /\ \A e \in log : \A k \in e.writes : store[k].ver >= e.ts
  /\ \A k \in Keys :
       store[k].ver # 0 =>
         \E e \in log : /\ e.ts = store[k].ver
                        /\ k \in e.writes
                        /\ e.client = store[k].writer

\* Transactions that have not finished commit expose nothing.
NoUncommittedVisible ==
  \A c \in Clients :
     cstate[c] \in {"active", "validating", "aborted", "committing"} =>
       \A k \in Keys : ~(store[k].writer = c /\ store[k].ver = commitTS[c]
                         /\ commitTS[c] # 0 /\ cstate[c] # "committed"
                         /\ cstate[c] # "idle"
                         /\ ~\E e \in log : e.client = c /\ e.ts = commitTS[c])

\* No lost updates: the current version of each key is the latest committed
\* write to it, so later reads see that write unless it is overwritten.
NoLostUpdates ==
  \A k \in Keys : store[k].ver = LatestBefore(k, MaxTS + 1)

\* Every read observes the initial version or a committed version.
ReadsSeeCommitted ==
  \A c \in Clients : \A k \in Keys :
     readVer[c][k] # NoRead =>
       \/ readVer[c][k] = 0
       \/ \E e \in log : e.ts = readVer[c][k] /\ k \in e.writes

\* At most one transaction holds an intent on a key. Intents belong only to
\* committing transactions.
IntentsWellFormed ==
  \A k \in Keys :
     intent[k] # NoClient =>
       /\ cstate[intent[k]] = "committing"
       /\ k \in wset[intent[k]]

\* Installed versions never go backwards in timestamp order.
MonotonicVersions ==
  [][\A k \in Keys : store'[k].ver >= store[k].ver]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

Pending(c) == cstate[c] \in {"active", "validating", "aborted"}

\* No other client is currently in the commit protocol.
QuietOthers(c) ==
  \A d \in Clients \ {c} : cstate[d] \notin {"validating", "committing"}

\* Progress: if conflicting commit activity eventually stops for good, a
\* client that keeps retrying eventually commits. The clock = MaxTS disjunct
\* only accounts for exhausting the bounded timestamp domain.
Progress ==
  \A c \in Clients :
     (<>[]QuietOthers(c)) =>
        (Pending(c) ~> (cstate[c] = "committed" \/ clock = MaxTS))

\* A transaction that passed validation always completes its commit.
CommitCompletes ==
  \A c \in Clients : (cstate[c] = "committing") ~> (cstate[c] = "committed")

-----------------------------------------------------------------------------
(* Symmetry: clients are interchangeable except for identity. *)

Perms == Permutations(Clients)

THEOREM Spec => [](TypeOK /\ UniqueCommitTS /\ Serializability /\ Atomicity
                   /\ NoLostUpdates /\ ReadsSeeCommitted /\ IntentsWellFormed)

=============================================================================