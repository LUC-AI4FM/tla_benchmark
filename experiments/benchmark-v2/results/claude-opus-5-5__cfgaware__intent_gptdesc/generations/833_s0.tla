\ m.type = "AcceptReply"
                                    /\ m.src = q
                                    /\ m.bal = b
                                    /\ m.slot = s
  /\ LET newInsts == [node[r].insts EXCEPT ![s].status = "Committed"]
     IN node' = [node EXCEPT ![r].insts = newInsts,
                             ![r].commitUpTo = CommitPrefix(newInsts)]
  /\ msgs' = msgs \cup
       {[type |-> "Commit", src |-> r, bal |-> b, slot |-> s,
         cmd  |-> node[r].insts[s].cmd]}
  /\ UNCHANGED clientVars

HandleCommit(r, m) ==
  /\ ~terminated
  /\ m \in msgs
  /\ m.type = "Commit"
  /\ node[r].insts[m.slot].status # "Committed"
  /\ LET newInsts == [node[r].insts EXCEPT ![m.slot].status = "Committed",
                                           ![m.slot].cmd = m.cmd]
     IN node' = [node EXCEPT ![r].insts = newInsts,
                             ![r].commitUpTo = CommitPrefix(newInsts)]
  /\ UNCHANGED <<msgs, pending, observed, reqsMade, acksRecv, terminated>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
Next ==
  \/ \E c \in Commands : ClientRequest(c)
  \/ \E c \in Commands : ClientAck(c)
  \/ \E r \in Replicas, b \in Ballots : BecomeLeader(r, b)
  \/ \E r \in Replicas, m \in msgs : HandlePrepare(r, m)
  \/ \E r \in Replicas : HandlePrepareReplies(r)
  \/ \E r \in Replicas, c \in Commands : TakeNewRequest(r, c)
  \/ \E r \in Replicas, s \in Slots : FillHole(r, s)
  \/ \E r \in Replicas, m \in msgs : HandleAccept(r, m)
  \/ \E r \in Replicas, s \in Slots : HandleAcceptReplies(r, s)
  \/ \E r \in Replicas, m \in msgs : HandleCommit(r, m)
  \/ Terminate
  \/ (terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
  /\ msgs \subseteq Messages
  /\ node \in [Replicas -> NodeStates]
  /\ pending \subseteq Commands
  /\ observed \in Seq(ClientEvents)
  /\ reqsMade \subseteq Commands
  /\ acksRecv \subseteq Commands
  /\ terminated \in BOOLEAN

QuorumIntersection ==
  \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Chosen(b, s) ==
  \E Q \in Quorums : \A q \in Q :
    \E m \in msgs : /\ m.type = "AcceptReply"
                    /\ m.src = q /\ m.bal = b /\ m.slot = s

\* Any commit is backed by a majority quorum of votes
CommittedOnQuorum ==
  \A m \in msgs : m.type = "Commit" => Chosen(m.bal, m.slot)

\* Proposals at higher ballots preserve previously chosen values
VotesPreserved ==
  \A m1, m2 \in msgs :
    (/\ m1.type = "Accept" /\ m2.type = "Accept"
     /\ m1.slot = m2.slot /\ m1.bal < m2.bal
     /\ Chosen(m1.bal, m1.slot)) => m2.cmd = m1.cmd

\* At most one Accept per (ballot, slot)
UniqueProposal ==
  \A m1, m2 \in msgs :
    (/\ m1.type = "Accept" /\ m2.type = "Accept"
     /\ m1.bal = m2.bal /\ m1.slot = m2.slot) => m1.cmd = m2.cmd

CommitAgreement ==
  \A r1, r2 \in Replicas, s \in Slots :
    (/\ node[r1].insts[s].status = "Committed"
     /\ node[r2].insts[s].status = "Committed")
      => node[r1].insts[s].cmd = node[r2].insts[s].cmd

ConsistentAcks ==
  \A i \in DOMAIN observed :
    observed[i].type = "Ack" =>
      \A r \in Replicas :
        observed[i].cmd \in Range(CommittedLog(r)) =>
          observed[i].val = AckVal(CommittedLog(r), observed[i].cmd)

RealTimeOrder ==
  \A i, j \in DOMAIN observed :
    (/\ i < j
     /\ observed[i].type = "Ack"
     /\ observed[j].type = "Req") =>
      \A r \in Replicas :
        LET log == CommittedLog(r) IN
          (observed[i].cmd \in Range(log) /\ observed[j].cmd \in Range(log))
            => FirstPos(log, observed[i].cmd) < FirstPos(log, observed[j].cmd)

Linearizability == ConsistentAcks /\ RealTimeOrder

Safety ==
  /\ QuorumIntersection
  /\ CommittedOnQuorum
  /\ VotesPreserved
  /\ UniqueProposal
  /\ CommitAgreement
  /\ Linearizability

(***************************************************************************)
(* Liveness (under FairSpec with eventual delivery)                         *)
(***************************************************************************)
AllAcked == <>(acksRecv = Commands)

=============================================================================
```