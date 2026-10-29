NCHANGED <<store, lockOwner, reads, buf, nack, msgs, log>>

RecvResp(c, m) ==
  /\ m \in msgs /\ m.dst = c /\ m.type \in RspTypes
  /\ \/ /\ m.type = "lockOk" /\ pc[c] = "lock"
        /\ resp' = [resp EXCEPT ![c] = @ \cup {m.k}]
        /\ UNCHANGED <<reads, nack>>
     \/ /\ m.type = "readResp" /\ pc[c] = "read"
        /\ resp' = [resp EXCEPT ![c] = @ \cup {m.k}]
        /\ reads' = [reads EXCEPT ![c][m.k] = m.val]
        /\ UNCHANGED nack
     \/ /\ m.type = "vote" /\ pc[c] = "validate" /\ m.ok
        /\ resp' = [resp EXCEPT ![c] = @ \cup {m.k}]
        /\ UNCHANGED <<reads, nack>>
     \/ /\ m.type = "vote" /\ pc[c] = "validate" /\ ~m.ok
        /\ nack' = [nack EXCEPT ![c] = @ \cup {m.k}]
        /\ UNCHANGED <<reads, resp>>
     \/ /\ m.type = "ack" /\ pc[c] = "commit"
        /\ resp' = [resp EXCEPT ![c] = @ \cup {m.k}]
        /\ UNCHANGED <<reads, nack>>
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<store, lockOwner, pc, txn, buf, log>>

\* Timeout-based retransmission of a lost request, sent directly to the primary.
Need(c) == CASE pc[c] = "read" -> RS[c]
             [] pc[c] \in {"lock", "validate", "commit"} -> Acc(c)
             [] OTHER -> {}
ReqOf(c) == CASE pc[c] = "lock" -> "lock"
              [] pc[c] = "read" -> "read"
              [] pc[c] = "validate" -> "prepare"
              [] OTHER -> "commit"
Payload(c) == CASE pc[c] = "validate" -> reads[c]
                [] pc[c] = "commit" -> buf[c]
                [] OTHER -> NoValF

Retransmit(c, k) ==
  /\ k \in Need(c) \ (resp[c] \cup nack[c])
  /\ ~\E m \in msgs : m.c = c /\ m.k = k
  /\ msgs' = msgs \cup {Msg(ReqOf(c), c, k, Primary[k], Payload(c)[k], TRUE)}
  /\ UNCHANGED <<store, lockOwner, pc, txn, reads, buf, resp, nack, log>>

-----------------------------------------------------------------------------
(* Replica actions *)

\* A non-primary replica forwards a request to the key's primary.
Forward(m) ==
  /\ m \in msgs /\ m.type \in ReqTypes /\ m.dst # Primary[m.k]
  /\ msgs' = (msgs \ {m}) \cup {[m EXCEPT !.dst = Primary[m.k]]}
  /\ UNCHANGED <<store, lockOwner, pc, txn, reads, buf, resp, nack, log>>

AtPrimary(m, t) == m \in msgs /\ m.type = t /\ m.dst = Primary[m.k]
Reply(m, t, v, ok) == Msg(t, m.c, m.k, m.c, v, ok)

HandleLock(m) ==
  /\ AtPrimary(m, "lock")
  /\ lockOwner[m.k] \in {NoClient, m.c}
  /\ lockOwner' = [lockOwner EXCEPT ![m.k] = m.c]
  /\ msgs' = (msgs \ {m}) \cup {Reply(m, "lockOk", NoVal, TRUE)}
  /\ UNCHANGED <<store, pc, txn, reads, buf, resp, nack, log>>

\* Reads see only committed state: blocked while another txn holds the key.
HandleRead(m) ==
  /\ AtPrimary(m, "read")
  /\ lockOwner[m.k] \in {NoClient, m.c}
  /\ msgs' = (msgs \ {m}) \cup {Reply(m, "readResp", store[m.k], TRUE)}
  /\ UNCHANGED <<store, lockOwner, pc, txn, reads, buf, resp, nack, log>>

\* OCC validation: key unlocked and the value read is still current.
HandlePrepare(m) ==
  /\ AtPrimary(m, "prepare")
  /\ LET ok == /\ lockOwner[m.k] = NoClient
               /\ (m.k \in RS[m.c] => store[m.k] = m.val)
     IN /\ lockOwner' = IF ok THEN [lockOwner EXCEPT ![m.k] = m.c] ELSE lockOwner
        /\ msgs' = (msgs \ {m}) \cup {Reply(m, "vote", NoVal, ok)}
  /\ UNCHANGED <<store, pc, txn, reads, buf, resp, nack, log>>

HandleCommit(m) ==
  /\ AtPrimary(m, "commit")
  /\ store' = IF m.val # NoVal /\ lockOwner[m.k] = m.c
              THEN [store EXCEPT ![m.k] = m.val] ELSE store
  /\ lockOwner' = IF lockOwner[m.k] = m.c
                  THEN [lockOwner EXCEPT ![m.k] = NoClient] ELSE lockOwner
  /\ msgs' = (msgs \ {m}) \cup {Reply(m, "ack", NoVal, TRUE)}
  /\ UNCHANGED <<pc, txn, reads, buf, resp, nack, log>>

HandleAbort(m) ==
  /\ AtPrimary(m, "abort")
  /\ lockOwner' = IF lockOwner[m.k] = m.c
                  THEN [lockOwner EXCEPT ![m.k] = NoClient] ELSE lockOwner
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<store, pc, txn, reads, buf, resp, nack, log>>

\* Unreliable replicas/channels may drop messages.
LoseMsg(m) ==
  /\ m \in msgs /\ m.dst \in Replicas \ Reliable
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<store, lockOwner, pc, txn, reads, buf, resp, nack, log>>

Done ==
  /\ \A c \in Clients : pc[c] = "idle" /\ txn[c] = MaxTxns
  /\ UNCHANGED vars

-----------------------------------------------------------------------------

ClientStep(c) ==
  \/ Begin(c) \/ LocksDone(c) \/ ReadsDone(c) \/ DoWrites(c)
  \/ OCDecide(c) \/ Finish(c)
  \/ \E k \in Keys : Retransmit(c, k)
  \/ \E m \in msgs : RecvResp(c, m)

ReplicaStep ==
  \E m \in msgs :
    \/ Forward(m) \/ HandleLock(m) \/ HandleRead(m) \/ HandlePrepare(m)
    \/ HandleCommit(m) \/ HandleAbort(m) \/ LoseMsg(m)

Next == (\E c \in Clients : ClientStep(c)) \/ ReplicaStep \/ Done

Fairness ==
  /\ \A c \in Clients :
       /\ WF_vars(Begin(c)) /\ WF_vars(LocksDone(c)) /\ WF_vars(ReadsDone(c))
       /\ WF_vars(DoWrites(c)) /\ WF_vars(OCDecide(c)) /\ WF_vars(Finish(c))
       /\ WF_vars(\E k \in Keys : Retransmit(c, k))
       /\ WF_vars(\E m \in msgs : RecvResp(c, m))
  /\ WF_vars(\E m \in msgs : Forward(m))
  /\ SF_vars(\E m \in msgs : HandleLock(m))
  /\ SF_vars(\E m \in msgs : HandleRead(m))
  /\ WF_vars(\E m \in msgs : HandlePrepare(m))
  /\ WF_vars(\E m \in msgs : HandleCommit(m))
  /\ WF_vars(\E m \in msgs : HandleAbort(m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

LastVal(i, k) ==
  LET J == {j \in 1..(i - 1) : log[j].wr[k] # NoVal}
  IN IF J = {} THEN InitVal
     ELSE log[CHOOSE j \in J : \A x \in J : x <= j].wr[k]

\* Every committed txn read exactly what the serial (commit-order) execution yields.
Serializability ==
  \A i \in 1..Len(log) : \A k \in Keys :
     log[i].rd[k] # NoVal => log[i].rd[k] = LastVal(i, k)

\* No two committed read-modify-writes on a key based on the same value,
\* and every committed write is reflected once the key is unlocked.
NoLostUpdate ==
  /\ \A i, j \in 1..Len(log) : \A k \in Keys :
       ~ ( /\ i # j
           /\ log[i].rd[k] # NoVal /\ log[i].wr[k] # NoVal
           /\ log[j].wr[k] # NoVal /\ log[j].rd[k] = log[i].rd[k] )
  /\ \A k \in Keys : lockOwner[k] = NoClient => store[k] = LastVal(Len(log) + 1, k)

TxnRead(c, k) == IF buf[c][k] # NoVal THEN buf[c][k] ELSE reads[c][k]

ReadYourWrites ==
  \A c \in Clients : \A k \in WS[c] :
     pc[c] \in {"validate", "commit"} => TxnRead(c, k) = MyVal(c)

\* Atomicity: a committed txn's writes are all-or-nothing visible.
Atomicity ==
  \A i \in 1..Len(log) : \A k1, k2 \in Keys :
     (log[i].wr[k1] # NoVal /\ log[i].wr[k2] # NoVal
      /\ lockOwner[k1] = NoClient /\ lockOwner[k2] = NoClient)
       => (store[k1] = log[i].wr[k1]) = (store[k2] = log[i].wr[k2])
          \/ \E j \in (i + 1)..Len(log) : log[j].wr[k1] # NoVal \/ log[j].wr[k2] # NoVal

Safety == TypeOK /\ Serializability /\ NoLostUpdate /\ ReadYourWrites /\ Atomicity

(* Liveness *)

\* A retrying optimistic transaction under bounded contention eventually commits.
OptimisticEventuallyCommits ==
  \A n \in 0..(MaxTxns - 1) :
     (txn[OC] = n /\ pc[OC] # "idle") ~> (txn[OC] = n + 1)

\* With a reliable majority (hosting the primaries), every client makes progress.
Progress == \A c \in Clients : <>(txn[c] = MaxTxns)

NoStuckTxn == \A c \in Clients : (pc[c] # "idle") ~> (pc[c] = "idle")

THEOREM Spec => []Safety
THEOREM Spec => (OptimisticEventuallyCommits /\ Progress /\ NoStuckTxn)
=============================================================================
```