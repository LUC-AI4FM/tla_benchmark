```tla
 {[type |-> "readReq", c |-> c,
                                     tid |-> nextTid + 1]}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars, snapVal, snapVer>>

(* Primary grants all requested locks atomically (all-or-nothing, so no   *)
(* circular wait), only if no other transaction holds a reservation on    *)
(* those keys at the primary.                                             *)
GrantLock(m) ==
    /\ m \in msgs
    /\ m.type = "lockReq"
    /\ \A k \in m.keys : /\ locks[k] = NoClient
                         /\ reserved[Primary[m.c]][k] = NoClient
    /\ locks'     = [k \in Keys |-> IF k \in m.keys THEN m.c ELSE locks[k]]
    /\ lockSince' = [k \in Keys |-> IF k \in m.keys THEN Len(history)
                                                   ELSE lockSince[k]]
    /\ msgs' = (msgs \ {m}) \cup
               {[type |-> "lockGrant", c |-> m.c, tid |-> m.tid]}
    /\ UNCHANGED <<repVars, cliVars, coordVars, histVars>>

ClientGetLock(c, m) ==
    /\ m \in msgs
    /\ m.type = "lockGrant"
    /\ m.c = c
    /\ cst[c] = "locking"
    /\ cst' = [cst EXCEPT ![c] = "reading"]
    /\ msgs' = (msgs \ {m}) \cup
               {[type |-> "readReq", c |-> c, tid |-> m.tid]}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars,
                   rset, wset, snapVal, snapVer, tid, nextTid>>

(* Primary serves a consistent snapshot of its whole copy in one step.    *)
PrimaryRead(m) ==
    /\ m \in msgs
    /\ m.type = "readReq"
    /\ msgs' = (msgs \ {m}) \cup
               {[type |-> "readResp", c |-> m.c, tid |-> m.tid,
                 vals |-> data[Primary[m.c]], vers |-> ver[Primary[m.c]]]}
    /\ UNCHANGED <<repVars, lockVars, cliVars, coordVars, histVars>>

ClientGetRead(c, m) ==
    /\ m \in msgs
    /\ m.type = "readResp"
    /\ m.c = c
    /\ cst[c] = "reading"
    /\ snapVal' = [snapVal EXCEPT ![c] = m.vals]
    /\ snapVer' = [snapVer EXCEPT ![c] = m.vers]
    /\ cst' = [cst EXCEPT ![c] = "executing"]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars,
                   rset, wset, tid, nextTid>>

(* Client proposes its writes (values f for keys in wset) to its primary. *)
ClientPropose(c, f) ==
    /\ cst[c] = "executing"
    /\ cst' = [cst EXCEPT ![c] = "waiting"]
    /\ msgs' = msgs \cup
         {[type |-> "propose", c |-> c, tid |-> tid[c],
           rk |-> rset[c], wk |-> wset[c], rv |-> snapVer[c],
           wv |-> [k \in Keys |-> IF k \in wset[c] THEN f[k]
                                                   ELSE snapVal[c][k]]]}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars,
                   rset, wset, snapVal, snapVer, tid, nextTid>>

(* Client voluntarily aborts before proposing (e.g. detected conflict).   *)
ClientAbort(c) ==
    /\ cst[c] = "executing"
    /\ cst' = [cst EXCEPT ![c] = "waiting"]
    /\ msgs' = msgs \cup {[type |-> "abortReq", c |-> c, tid |-> tid[c]]}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars,
                   rset, wset, snapVal, snapVer, tid, nextTid>>

-----------------------------------------------------------------------------
(* Coordinator (primary of m.c) starts two-phase commit.                   *)
CoordPropose(m) ==
    /\ m \in msgs
    /\ m.type = "propose"
    /\ cphase[m.c] = "idle"
    /\ prop'   = [prop EXCEPT ![m.c] = [tid |-> m.tid, rk |-> m.rk,
                                        wk |-> m.wk, rv |-> m.rv,
                                        wv |-> m.wv]]
    /\ cphase' = [cphase EXCEPT ![m.c] = "voting"]
    /\ votes'  = [votes EXCEPT ![m.c] = [r \in Replicas |-> "none"]]
    /\ acks'   = [acks EXCEPT ![m.c] = {}]
    /\ msgs' = (msgs \ {m}) \cup
         {[type |-> "prepare", c |-> m.c, tid |-> m.tid, rep |-> r,
           keys |-> m.rk \cup m.wk, rv |-> m.rv] : r \in Replicas}
    /\ UNCHANGED <<repVars, lockVars, cliVars, histVars>>

(* Coordinator handles a client abort: no replica state was touched.      *)
CoordAbortReq(m) ==
    /\ m \in msgs
    /\ m.type = "abortReq"
    /\ cphase[m.c] = "idle"
    /\ abortedTids' = abortedTids \cup {m.tid}
    /\ ReleaseLocks(m.c)
    /\ msgs' = (msgs \ {m}) \cup
               {[type |-> "outcome", c |-> m.c, tid |-> m.tid,
                 commit |-> FALSE]}
    /\ UNCHANGED <<repVars, lockSince, cliVars, coordVars,
                   history, committedTids>>
```

```tla
(* Replica votes: yes iff its versions match the snapshot, keys are not   *)
(* reserved by another transaction, and not locked by another client.     *)
ReplicaPrepare(r, m) ==
    /\ m \in msgs
    /\ m.type = "prepare"
    /\ m.rep = r
    /\ LET ok == \A k \in m.keys : /\ ver[r][k] = m.rv[k]
                                  /\ reserved[r][k] = NoClient
                                  /\ locks[k] \in {NoClient, m.c}
       IN /\ reserved' = IF ok
                           THEN [reserved EXCEPT ![r] =
                                   [k \in Keys |-> IF k \in m.keys THEN m.c
                                                   ELSE reserved[r][k]]]
                           ELSE reserved
          /\ msgs' = (msgs \ {m}) \cup
                     {[type |-> "vote", c |-> m.c, tid |-> m.tid,
                       rep |-> r, yes |-> ok]}
    /\ UNCHANGED <<data, ver, applied, lockVars, cliVars, coordVars, histVars>>

CoordVote(m) ==
    /\ m \in msgs
    /\ m.type = "vote"
    /\ cphase[m.c] = "voting"
    /\ m.tid = prop[m.c].tid
    /\ votes' = [votes EXCEPT ![m.c][m.rep] = IF m.yes THEN "yes" ELSE "no"]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<repVars, lockVars, cliVars, histVars, cphase, acks, prop>>

(* Coordinator decides once all votes are in; commit iff all voted yes.  *)
CoordDecide(c) ==
    /\ cphase[c] = "voting"
    /\ \A r \in Replicas : votes[c][r] # "none"
    /\ LET commit == \A r \in Replicas : votes[c][r] = "yes"
           p      == prop[c]
       IN /\ history' = IF commit
                          THEN Append(history,
                                 [tid |-> p.tid, client |-> c,
                                  keys |-> p.rk \cup p.wk, wk |-> p.wk,
                                  rv |-> p.rv, wv |-> p.wv])
                          ELSE history
          /\ committedTids' = IF commit THEN committedTids \cup {p.tid}
                                        ELSE committedTids
          /\ abortedTids'   = IF commit THEN abortedTids
                                        ELSE abortedTids \cup {p.tid}
          /\ msgs' = msgs \cup
               {[type |-> "decision", c |-> c, tid |-> p.tid, rep |-> r,
                 commit |-> commit, wk |-> p.wk, wv |-> p.wv] : r \in Replicas}
    /\ cphase' = [cphase EXCEPT ![c] = "acking"]
    /\ acks'   = [acks EXCEPT ![c] = {}]
    /\ UNCHANGED <<repVars, lockVars, cliVars, votes, prop>>

(* Replica applies a commit atomically (all writes in one step) or       *)
(* discards an abort; in both cases it releases the reservation.         *)
ReplicaDecision(r, m) ==
    /\ m \in msgs
    /\ m.type = "decision"
    /\ m.rep = r
    /\ data' = IF m.commit
                 THEN [data EXCEPT ![r] = [k \in Keys |->
                         IF k \in m.wk THEN m.wv[k] ELSE data[r][k]]]
                 ELSE data
    /\ ver' = IF m.commit
                THEN [ver EXCEPT ![r] = [k \in Keys |->
                        IF k \in m.wk THEN ver[r][k] + 1 ELSE ver[r][k]]]
                ELSE ver
    /\ applied' = IF m.commit THEN [applied EXCEPT ![r] = @ \cup {m.tid}]
                              ELSE applied
    /\ reserved' = [reserved EXCEPT ![r] = [k \in Keys |->
                      IF reserved[r][k] = m.c THEN NoClient
                                              ELSE reserved[r][k]]]
    /\ msgs' = (msgs \ {m}) \cup
               {[type |-> "ack", c |-> m.c, tid |-> m.tid, rep |-> r]}
    /\ UNCHANGED <<lockVars, cliVars, coordVars, histVars>>

CoordAck(m) ==
    /\ m \in msgs
    /\ m.type = "ack"
    /\ cphase[m.c] = "acking"
    /\ m.tid = prop[m.c].tid
    /\ acks' = [acks EXCEPT ![m.c] = @ \cup {m.rep}]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<repVars, lockVars, cliVars, histVars, cphase, votes, prop>>

(* After all replicas applied the decision, release locks and notify.    *)
CoordFinish(c) ==
    /\ cphase[c] = "acking"
    /\ acks[c] = Replicas
    /\ ReleaseLocks(c)
    /\ cphase' = [cphase EXCEPT ![c] = "idle"]
    /\ msgs' = msgs \cup
               {[type |-> "outcome", c |-> c, tid |-> prop[c].tid,
                 commit |-> prop[c].tid \in committedTids]}
    /\ UNCHANGED <<repVars, lockSince, cliVars, histVars, votes, acks, prop>>

ClientOutcome(c, m) ==
    /\ m \in msgs
    /\ m.type = "outcome"
    /\ m.c = c
    /\ cst[c] = "waiting"
    /\ cst' = [cst EXCEPT ![c] = "done"]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<repVars, lockVars, coordVars, histVars,
                   rset, wset, snapVal, snapVer, tid, nextTid>>
```

```tla
-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Clients, R \in SUBSET Keys, W \in SUBSET Keys : Begin(c, R, W)
    \/ \E m \in msgs : GrantLock(m)
    \/ \E c \in Clients, m \in msgs : ClientGetLock(c, m)
    \/ \E m \in msgs : PrimaryRead(m)
    \/ \E c \in Clients, m \in msgs : ClientGetRead(c, m)
    \/ \E c \in Clients : \E f \in [wset[c] -> Values] : ClientPropose(c, f)
    \/ \E c \in Clients : ClientAbort(c)
    \/ \E m \in msgs : CoordPropose(m)
    \/ \E m \in msgs : CoordAbortReq(m)
    \/ \E r \in Replicas, m \in msgs : ReplicaPrepare(r, m)
    \/ \E m \in msgs : CoordVote(m)
    \/ \E c \in Clients : CoordDecide(c)
    \/ \E r \in Replicas, m \in msgs : ReplicaDecision(r, m)
    \/ \E m \in msgs : CoordAck(m)
    \/ \E c \in Clients : CoordFinish(c)
    \/ \E c \in Clients, m \in msgs : ClientOutcome(c, m)

(* Nonfaulty clients and primaries make progress; messages are          *)
(* eventually delivered. Lock grants need strong fairness since a lock   *)
(* request is only intermittently grantable.                             *)
Fairness ==
    /\ \A c \in Clients :
        /\ SF_vars(\E m \in msgs : m.c = c /\ GrantLock(m))
        /\ WF_vars(\E m \in msgs : ClientGetLock(c, m))
        /\ WF_vars(\E m \in msgs : m.c = c /\ PrimaryRead(m))
        /\ WF_vars(\E m \in msgs : ClientGetRead(c, m))
        /\ WF_vars((\E f \in [wset[c] -> Values] : ClientPropose(c, f))
                   \/ ClientAbort(c))
        /\ WF_vars(\E m \in msgs : m.c = c /\ CoordPropose(m))
        /\ WF_vars(\E m \in msgs : m.c = c /\ CoordAbortReq(m))
        /\ WF_vars(\E m \in msgs : m.c = c /\ CoordVote(m))
        /\ WF_vars(CoordDecide(c))
        /\ WF_vars(\E m \in msgs : m.c = c /\ CoordAck(m))
        /\ WF_vars(CoordFinish(c))
        /\ WF_vars(\E m \in msgs : ClientOutcome(c, m))
    /\ \A r \in Replicas, c \in Clients :
        /\ WF_vars(\E m \in msgs : m.c = c /\ ReplicaPrepare(r, m))
        /\ WF_vars(\E m \in msgs : m.c = c /\ ReplicaDecision(r, m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Helpers over the commit history (commit order = serial order).        *)
NV(i, k) == Cardinality({j \in 1..i : k \in history[j].wk})

TypeOK ==
    /\ data \in [Replicas -> [Keys -> Values]]
    /\ ver \in [Replicas -> [Keys -> Nat]]
    /\ reserved \in [Replicas -> [Keys -> Holder]]
    /\ locks \in [Keys -> Holder]
    /\ lockSince \in [Keys -> Nat]
    /\ cst \in [Clients -> ClientPhases]
    /\ rset \in [Clients -> SUBSET Keys]
    /\ wset \in [Clients -> SUBSET Keys]
    /\ cphase \in [Clients -> {"idle", "voting", "acking"}]
    /\ votes \in [Clients -> [Replicas -> {"none", "yes", "no"}]]
    /\ acks \in [Clients -> SUBSET Replicas]
    /\ nextTid \in 0..MaxTxns

(* (1) Atomicity: a committed transaction's writes become visible at a   *)
(* replica all together or not at all; nothing is both committed and     *)
(* aborted.                                                              *)
Atomicity ==
    /\ committedTids \cap abortedTids = {}
    /\ \A r \in Replicas, i \in 1..Len(history) :
         LET h == history[i] IN
           /\ h.tid \in applied[r] => \A k \in h.wk : ver[r][k] >= NV(i, k)
           /\ h.tid \notin applied[r] => \A k \in h.wk : ver[r][k] < NV(i, k)

(* Aborted transactions leave state unchanged: replica state is exactly  *)
(* the effect of the committed transactions it has applied.              *)
AbortedNoEffect ==
    \A r \in Replicas :
      /\ applied[r] \subseteq committedTids
      /\ \A k \in Keys :
           LET W == {i \in 1..Len(history) :
                        history[i].tid \in applied[r] /\ k \in history[i].wk}
           IN /\ ver[r][k] = Cardinality(W)
              /\ data[r][k] = IF W = {} THEN InitVal
                                        ELSE history[Max(W)].wv[k]

(* (2) Serializability: each committed transaction read exactly the      *)
(* state produced by the committed transactions serialized before it.    *)
Serializability ==
    \A i \in 1..Len(history) :
      \A k \in history[i].keys :
        history[i].rv[k] = Cardinality({j \in 1..(i - 1) : k \in history[j].wk})

(* (3) No lost updates: a later committed writer of k observed the      *)
(* effect of every earlier committed writer of k.                       *)
NoLostUpdate ==
    \A i, j \in 1..Len(history) :
      i < j => \A k \in history[i].wk \cap history[j].wk :
                 history[j].rv[k] >= NV(i, k)

(* (4) Lock safety: locks are exclusive and held only by pessimistic     *)
(* clients; while held, no other client commits a conflicting txn.      *)
LockSafety ==
    \A k \in Keys :
      /\ locks[k] \in PessClients \cup {NoClient}
      /\ locks[k] # NoClient =>
           \A i \in (lockSince[k] + 1)..Len(history) :
             k \in history[i].keys => history[i].client = locks[k]

Safety == TypeOK /\ Atomicity /\ AbortedNoEffect /\ Serializability
          /\ NoLostUpdate /\ LockSafety

-----------------------------------------------------------------------------
(* Liveness *)
ClientProgress == \A c \in Clients : (cst[c] \in Active) ~> (cst[c] = "done")
CoordProgress  == \A c \in Clients : (cphase[c] # "idle") ~> (cphase[c] = "idle")
LockRelease    == \A k \in Keys : (locks[k] # NoClient) ~> (locks[k] = NoClient)
NoPermanentDeadlock == <>[](\A c \in Clients : cst[c] \notin Active) \/
                       []<>(\E c \in Clients : cst[c] \notin Active)
MessagesDelivered == (nextTid = MaxTxns) ~> (msgs = {})

THEOREM Spec => []Safety
THEOREM Spec => ClientProgress /\ CoordProgress /\ LockRelease
=============================================================================
```