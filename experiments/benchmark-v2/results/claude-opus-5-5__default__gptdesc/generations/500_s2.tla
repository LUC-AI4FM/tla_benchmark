```tla
==
  /\ pc[r] = "rloop"
  /\ node[r].leader = r
  /\ node[r].balMaxKnown > 0
  /\ node[r].balPrepared # node[r].balMaxKnown
  /\ LET b       == node[r].balMaxKnown
         replies == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
     IN  /\ Cardinality({m.src : m \in replies}) >= MajorityNum
         /\ LET newInsts ==
                  [s \in Slots |->
                     RecoverInst(node[r].insts[s], {m.voted[s] : m \in replies})]
                accSlots == {t \in Slots : newInsts[t].status = "Accepting"}
                comSlots == {t \in Slots : newInsts[t].status = "Committed"}
            IN  /\ node' = [node EXCEPT ![r].balPrepared = b,
                                        ![r].insts = newInsts]
                /\ msgs' = msgs
                     \cup {[type |-> "Accept", src |-> r, bal |-> b,
                            slot |-> s, cmd |-> newInsts[s].cmd] : s \in accSlots}
                     \cup {[type |-> "CommitNotice", slot |-> s,
                            cmd |-> newInsts[s].cmd] : s \in comSlots}
  /\ UNCHANGED <<pending, requested, observed, pc>>

TakeNewRequest(r) ==
  /\ pc[r] = "rloop"
  /\ IsPrepared(r)
  /\ \E c \in pending :
       /\ ~\E t \in Slots : node[r].insts[t].cmd = c
       /\ \E s \in Slots :
            /\ node[r].insts[s].status = "Empty"
            /\ \A t \in 1..(s-1) : node[r].insts[t].status # "Empty"
            /\ node' = [node EXCEPT ![r].insts[s] =
                          [status |-> "Accepting", cmd |-> c,
                           voted  |-> node[r].insts[s].voted]]
            /\ msgs' = msgs \cup
                 {[type |-> "Accept", src |-> r, bal |-> node[r].balMaxKnown,
                   slot |-> s, cmd |-> c]}
  /\ UNCHANGED <<pending, requested, observed, pc>>

HandleAccept(r) ==
  /\ pc[r] = "rloop"
  /\ \E m \in msgs :
       /\ m.type = "Accept"
       /\ m.bal >= node[r].balMaxKnown
       /\ [type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot]
            \notin msgs
       /\ node' = [node EXCEPT
                     ![r].leader = m.src,
                     ![r].balMaxKnown = m.bal,
                     ![r].balPrepared =
                         IF m.src = r THEN node[r].balPrepared ELSE 0,
                     ![r].insts[m.slot] =
                         IF node[r].insts[m.slot].status = "Committed"
                           THEN [node[r].insts[m.slot] EXCEPT
                                   !.voted = [bal |-> m.bal, cmd |-> m.cmd]]
                           ELSE [status |-> "Accepting", cmd |-> m.cmd,
                                 voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
       /\ msgs' = msgs \cup
            {[type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot]}
  /\ UNCHANGED <<pending, requested, observed, pc>>

HandleAcceptReplies(r) ==
  /\ pc[r] = "rloop"
  /\ IsPrepared(r)
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Accepting"
       /\ Cardinality({m.src : m \in
             {m2 \in msgs : /\ m2.type = "AcceptReply"
                            /\ m2.bal = node[r].balMaxKnown
                            /\ m2.slot = s}}) >= MajorityNum
       /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
       /\ msgs' = msgs \cup
            {[type |-> "CommitNotice", slot |-> s, cmd |-> node[r].insts[s].cmd]}
  /\ UNCHANGED <<pending, requested, observed, pc>>

HandleCommitNotice(r) ==
  /\ pc[r] = "rloop"
  /\ \E m \in msgs :
       /\ m.type = "CommitNotice"
       /\ node[r].insts[m.slot].status # "Committed"
       /\ node' = [node EXCEPT ![r].insts[m.slot] =
                     [status |-> "Committed", cmd |-> m.cmd,
                      voted  |-> node[r].insts[m.slot].voted]]
  /\ UNCHANGED <<msgs, pending, requested, observed, pc>>

Execute(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].commitUpTo < NumCommands
  /\ LET s      == node[r].commitUpTo + 1
         c      == node[r].insts[s].cmd
         dup    == \E t \in 1..(s-1) : node[r].insts[t].cmd = c
         newVal == IF ~dup /\ c \in Writes THEN c ELSE node[r].kvalue
     IN  /\ node[r].insts[s].status = "Committed"
         /\ node' = [node EXCEPT ![r].commitUpTo = s, ![r].kvalue = newVal]
         /\ IF ~dup /\ c \in pending
              THEN /\ observed' = Append(observed,
                                    [type |-> "ack", cmd |-> c, val |-> newVal])
                   /\ pending' = pending \ {c}
              ELSE UNCHANGED <<observed, pending>>
  /\ UNCHANGED <<msgs, requested, pc>>

Finish(r) ==
  /\ pc[r] = "rloop"
  /\ \A c \in Commands :
       \E s \in 1..node[r].commitUpTo : node[r].insts[s].cmd = c
  /\ pc' = [pc EXCEPT ![r] = "Done"]
  /\ UNCHANGED <<msgs, node, pending, requested, observed>>

ReplicaStep(r) ==
  \/ BecomeLeader(r)
  \/ HandlePrepare(r)
  \/ HandlePrepareReplies(r)
  \/ TakeNewRequest(r)
  \/ HandleAccept(r)
  \/ HandleAcceptReplies(r)
  \/ HandleCommitNotice(r)
  \/ Execute(r)
  \/ Finish(r)

(* Explicit stuttering after termination to avoid deadlock *)
Terminating ==
  /\ \A r \in Replicas : pc[r] = "Done"
  /\ UNCHANGED vars

Next ==
  \/ ClientRequest
  \/ \E r \in Replicas : ReplicaStep(r)
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ClientRequest)
  /\ \A r \in Replicas : WF_vars(ReplicaStep(r))

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
  /\ msgs \subseteq Messages
  /\ node \in [Replicas -> NodeStates]
  /\ pending \subseteq Commands
  /\ requested \subseteq Commands
  /\ observed \in Seq(ClientEvents)
  /\ pc \in [Replicas -> {"rloop", "Done"}]

CommittedAgreement ==
  \A r1, r2 \in Replicas, s \in Slots :
    (/\ node[r1].insts[s].status = "Committed"
     /\ node[r2].insts[s].status = "Committed")
      => node[r1].insts[s].cmd = node[r2].insts[s].cmd

CommitNoticeAgreement ==
  \A m1, m2 \in msgs :
    (/\ m1.type = "CommitNotice"
     /\ m2.type = "CommitNotice"
     /\ m1.slot = m2.slot)
      => m1.cmd = m2.cmd

AckAfterReq ==
  \A i \in 1..Len(observed) :
    observed[i].type = "ack" =>
      \E j \in 1..(i-1) : /\ observed[j].type = "req"
                          /\ observed[j].cmd = observed[i].cmd

AckAtMostOnce ==
  \A i, j \in 1..Len(observed) :
    (/\ observed[i].type = "ack"
     /\ observed[j].type = "ack"
     /\ observed[i].cmd = observed[j].cmd)
      => i = j

WriteAckValue ==
  \A i \in 1..Len(observed) :
    (observed[i].type = "ack" /\ observed[i].cmd \in Writes)
      => observed[i].val = observed[i].cmd

ReadAckValue ==
  \A i \in 1..Len(observed) :
    (observed[i].type = "ack" /\ observed[i].cmd \in Reads)
      => \/ observed[i].val = Nil
         \/ \E j \in 1..(i-1) : /\ observed[j].type = "req"
                                /\ observed[j].cmd = observed[i].val

ReadAfterWriteAck ==
  \A i, j, k \in 1..Len(observed) :
    (/\ i < j /\ j < k
     /\ observed[i].type = "ack" /\ observed[i].cmd \in Writes
     /\ observed[j].type = "req" /\ observed[j].cmd \in Reads
     /\ observed[k].type = "ack" /\ observed[k].cmd = observed[j].cmd)
      => observed[k].val # Nil

Safety ==
  /\ TypeOK
  /\ CommittedAgreement
  /\ CommitNoticeAgreement
  /\ AckAfterReq
  /\ AckAtMostOnce
  /\ WriteAckValue
  /\ ReadAckValue
  /\ ReadAfterWriteAck

-----------------------------------------------------------------------------
(* Liveness: all replica processes eventually terminate *)

Termination == <>(\A r \in Replicas : pc[r] = "Done")

=============================================================================
```