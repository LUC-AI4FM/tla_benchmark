```tla
up {MkMsg("Accept", r, NullNode, b, s, c, NoVotes)}
        /\ UNCHANGED <<pending, observed>>

\* Acceptor r handles an Accept, voting for the command.
HandleAccept(r, m) ==
    /\ m \in msgs
    /\ m.type = "Accept"
    /\ m.bal >= node[r].balMaxKnown
    /\ ~ \E m2 \in msgs : /\ m2.type = "AcceptReply"
                          /\ m2.src = r /\ m2.bal = m.bal /\ m2.slot = m.slot
    /\ node' = [node EXCEPT
                  ![r].balMaxKnown = m.bal,
                  ![r].balPrepared = IF m.bal > node[r].balMaxKnown
                                     THEN 0 ELSE node[r].balPrepared,
                  ![r].insts[m.slot] =
                      IF node[r].insts[m.slot].status = "Committed"
                      THEN [node[r].insts[m.slot] EXCEPT
                              !.voted = [bal |-> m.bal, cmd |-> m.cmd]]
                      ELSE [status |-> "Accepting", cmd |-> m.cmd,
                            voted |-> [bal |-> m.bal, cmd |-> m.cmd]]]
    /\ msgs' = msgs \cup
         {MkMsg("AcceptReply", r, m.src, m.bal, m.slot, m.cmd, NoVotes)}
    /\ UNCHANGED <<pending, observed>>

\* Leader r commits slot s after a majority of AcceptReplies.
AcceptFinish(r, s) ==
    LET b == node[r].balPrepared
        replies == {m \in msgs : /\ m.type = "AcceptReply"
                                 /\ m.dst = r /\ m.bal = b /\ m.slot = s}
    IN  /\ IsLeader(r)
        /\ node[r].insts[s].status = "Accepting"
        /\ node[r].insts[s].voted.bal = b
        /\ \E Q \in Quorums : \A q \in Q : \E m \in replies : m.src = q
        /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
        /\ msgs' = msgs \cup
             {MkMsg("CommitNotice", r, NullNode, b, s,
                    node[r].insts[s].cmd, NoVotes)}
        /\ UNCHANGED <<pending, observed>>

\* Replica r learns that a slot has been committed.
HandleCommitNotice(r, m) ==
    /\ m \in msgs
    /\ m.type = "CommitNotice"
    /\ node[r].insts[m.slot].status # "Committed"
    /\ node' = [node EXCEPT ![r].insts[m.slot] =
                  [status |-> "Committed", cmd |-> m.cmd,
                   voted |-> node[r].insts[m.slot].voted]]
    /\ UNCHANGED <<msgs, pending, observed>>

\* Value of the key just before executing slot s; duplicate entries of a
\* command in the log are ignored (only the first occurrence executes).
FirstOcc(insts, t) == \A u \in 1..(t - 1) : insts[u].cmd # insts[t].cmd

LastWrite(insts, s) ==
    LET ws == {t \in 1..(s - 1) : insts[t].cmd \in Writes /\ FirstOcc(insts, t)}
    IN  IF ws = {} THEN NullVal
        ELSE insts[CHOOSE t \in ws : \A u \in ws : u <= t].cmd

\* Leader r executes a committed slot (all previous slots committed) and
\* acknowledges the client exactly once (idempotency).
Reply(r, s) ==
    LET inst == node[r].insts[s]
        c    == inst.cmd
    IN  /\ IsLeader(r)
        /\ inst.status = "Committed"
        /\ c \in Commands
        /\ \A t \in 1..(s - 1) : node[r].insts[t].status = "Committed"
        /\ FirstOcc(node[r].insts, s)
        /\ ~ Acked(c)
        /\ observed' = Append(observed,
               AckEvent(c, IF c \in Writes THEN c
                           ELSE LastWrite(node[r].insts, s)))
        /\ UNCHANGED <<msgs, node, pending>>

-----------------------------------------------------------------------------
(******************************* Spec *************************************)

AllDone == pending = {} /\ \A c \in Commands : Acked(c)

\* Stuttering allowed only after all requests have been observed, so any
\* earlier deadlock is reported by the model checker.
Terminating == AllDone /\ UNCHANGED vars

Next ==
    \/ \E c \in Commands : ClientRequest(c)
    \/ \E r \in Replicas :
          \/ \E b \in Ballots : BecomeLeader(r, b)
          \/ \E m \in msgs : HandlePrepare(r, m)
          \/ PrepareFinish(r)
          \/ \E s \in Slots, c \in Commands \cup {NoOp} : Propose(r, s, c)
          \/ \E m \in msgs : HandleAccept(r, m)
          \/ \E s \in Slots : AcceptFinish(r, s)
          \/ \E m \in msgs : HandleCommitNotice(r, m)
          \/ \E s \in Slots : Reply(r, s)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(****************************** Properties *******************************)

\* Committed log entries agree across all replicas.
ConsistentLogs ==
    \A r1, r2 \in Replicas, s \in Slots :
        (/\ node[r1].insts[s].status = "Committed"
         /\ node[r2].insts[s].status = "Committed")
        => node[r1].insts[s].cmd = node[r2].insts[s].cmd

\* Each command is acknowledged at most once and only after its request.
AckOnceAfterReq ==
    \A i \in 1..Len(observed) :
        observed[i].type = "Ack" =>
            /\ \E j \in 1..(i - 1) : observed[j].type = "Req"
                                     /\ observed[j].cmd = observed[i].cmd
            /\ \A k \in 1..Len(observed) :
                   (k # i /\ observed[k].type = "Ack")
                   => observed[k].cmd # observed[i].cmd

\* Linearizability from the client's perspective: there is a total order
\* of all acknowledged (plus possibly some pending) commands that respects
\* real-time order and in which every read returns the latest write.
Linearizable ==
    LET requested == {c \in Commands : Requested(c)}
        acked     == {c \in Commands : Acked(c)}
        AckIdx(c) == CHOOSE i \in 1..Len(observed) :
                        observed[i].type = "Ack" /\ observed[i].cmd = c
        ReqIdx(c) == CHOOSE i \in 1..Len(observed) :
                        observed[i].type = "Req" /\ observed[i].cmd = c
        AckVal(c) == observed[AckIdx(c)].val
    IN  \E S \in SUBSET requested :
          /\ acked \subseteq S
          /\ \E ord \in [1..Cardinality(S) -> S] :
               /\ \A i, j \in 1..Cardinality(S) : i # j => ord[i] # ord[j]
               /\ \A i, j \in 1..Cardinality(S) :
                     (ord[i] \in acked /\ AckIdx(ord[i]) < ReqIdx(ord[j]))
                     => i < j
               /\ \A i \in 1..Cardinality(S) :
                     (ord[i] \in Reads /\ ord[i] \in acked) =>
                        LET ws == {j \in 1..(i - 1) : ord[j] \in Writes}
                        IN  AckVal(ord[i]) =
                              IF ws = {} THEN NullVal
                              ELSE ord[CHOOSE j \in ws : \A k \in ws : k <= j]

\* Liveness: eventually all requests are made and acknowledged.
EventuallyAllObserved == <>AllDone

=============================================================================
```