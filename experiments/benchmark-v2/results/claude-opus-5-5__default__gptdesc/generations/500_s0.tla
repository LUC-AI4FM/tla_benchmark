) == CHOOSE v \in S : \A w \in S : w.bal <= v.bal

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Type invariant                                                          *)
-----------------------------------------------------------------------------

InstType == [status : Statuses,
             cmd    : AllCmds,
             voted  : [bal : 0..MaxBallot, cmd : AllCmds]]

NodeType == [balPrepared : 0..MaxBallot,
             balMaxKnown : 0..MaxBallot,
             commitUpTo  : 0..NumSlots,
             kvalue      : Writes \cup {Nil},
             insts       : [Slots -> InstType]]

EventType == [type : {"Req", "Ack"},
              cmd  : Commands,
              val  : Writes \cup {Nil}]

TypeOK == /\ node \in [Replicas -> NodeType]
          /\ pc \in [Replicas -> {"rloop", "Done"}]
          /\ observed \in Seq(EventType)

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ node = [r \in Replicas |->
                     [balPrepared |-> NullBallot,
                      balMaxKnown |-> NullBallot,
                      commitUpTo  |-> 0,
                      kvalue      |-> Nil,
                      insts       |-> [s \in Slots |-> NullInst]]]
        /\ pc = [r \in Replicas |-> "rloop"]
        /\ observed = <<>>

-----------------------------------------------------------------------------
(* Client action: issue a new request                                      *)
-----------------------------------------------------------------------------

ClientRequest(c) ==
    /\ c \in Commands
    /\ c \notin Requested
    /\ observed' = Append(observed, ReqEvent(c))
    /\ UNCHANGED <<msgs, node, pc>>

-----------------------------------------------------------------------------
(* Phase 1: Prepare                                                        *)
-----------------------------------------------------------------------------

\* Replica r tries to become leader with a ballot b that it owns.
Prepare(r, b) ==
    /\ pc[r] = "rloop"
    /\ b \in Ballots
    /\ BallotOwner(b) = r
    /\ b > node[r].balMaxKnown
    /\ node' = [node EXCEPT ![r].balMaxKnown = b]
    /\ Send([type |-> "Prepare", src |-> r, bal |-> b])
    /\ UNCHANGED <<pc, observed>>

\* Replica r promises ballot m.bal and reports its votes for all slots.
HandlePrepare(r, m) ==
    /\ pc[r] = "rloop"
    /\ m \in msgs
    /\ m.type = "Prepare"
    /\ m.bal >= node[r].balMaxKnown
    /\ LET reply == [type  |-> "PrepareReply",
                     src   |-> r,
                     bal   |-> m.bal,
                     votes |-> [s \in Slots |-> node[r].insts[s].voted]]
       IN /\ reply \notin msgs
          /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal]
          /\ Send(reply)
    /\ UNCHANGED <<pc, observed>>

\* Replica r gathers a majority of PrepareReplies for its ballot, becomes
\* leader, adopts the highest-ballot vote for each uncommitted slot, and
\* re-proposes those commands with Accept messages.
BecomeLeader(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ b \in Ballots
    /\ BallotOwner(b) = r
    /\ node[r].balPrepared # b
    /\ \E Q \in SUBSET Replicas :
         /\ Cardinality(Q) >= MajorityNum
         /\ \A q \in Q : \E pm \in msgs :
               /\ pm.type = "PrepareReply"
               /\ pm.src = q
               /\ pm.bal = b
         /\ LET replies == {rm \in msgs : /\ rm.type = "PrepareReply"
                                          /\ rm.bal = b
                                          /\ rm.src \in Q}
                VotesAt(s) == {v \in {rm.votes[s] : rm \in replies} :
                                  v.bal > NullBallot}
                OldInst(s) == node[r].insts[s]
                newInsts ==
                  [s \in Slots |->
                     IF OldInst(s).status = "Committed"
                       THEN OldInst(s)
                       ELSE IF VotesAt(s) = {}
                              THEN [status |-> "Empty",
                                    cmd    |-> NullCmd,
                                    voted  |-> OldInst(s).voted]
                              ELSE [status |-> "Accepting",
                                    cmd    |-> HighestVote(VotesAt(s)).cmd,
                                    voted  |-> OldInst(s).voted]]
                acceptSlots == {s \in Slots : newInsts[s].status = "Accepting"}
            IN /\ node' = [node EXCEPT ![r].balPrepared = b,
                                       ![r].insts = newInsts]
               /\ msgs' = msgs \cup
                    {[type |-> "Accept", src |-> r, bal |-> b,
                      slot |-> s, cmd |-> newInsts[s].cmd] : s \in acceptSlots}
    /\ UNCHANGED <<pc, observed>>

-----------------------------------------------------------------------------
(* Phase 2: Accept                                                         *)
-----------------------------------------------------------------------------

Propose(r, s, c) ==
    /\ node' = [node EXCEPT ![r].insts[s].status = "Accepting",
                            ![r].insts[s].cmd = c]
    /\ Send([type |-> "Accept", src |-> r, bal |-> node[r].balPrepared,
             slot |-> s, cmd |-> c])

\* Leader places a requested, not-yet-logged command into the first empty slot.
TakeNewRequest(r, c) ==
    /\ pc[r] = "rloop"
    /\ IsLeader(r)
    /\ c \in Requested
    /\ \A s \in Slots : node[r].insts[s].cmd # c
    /\ \E s \in Slots :
         /\ node[r].insts[s].status = "Empty"
         /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
         /\ Propose(r, s, c)
    /\ UNCHANGED <<pc, observed>>

\* Leader fills a hole in the log (below a non-empty slot) with a no-op.
FillGap(r, s) ==
    /\ pc[r] = "rloop"
    /\ IsLeader(r)
    /\ s \in Slots
    /\ node[r].insts[s].status = "Empty"
    /\ \E t \in Slots : t > s /\ node[r].insts[t].status # "Empty"
    /\ Propose(r, s, NoOp)
    /\ UNCHANGED <<pc, observed>>

\* Acceptor r votes for the proposal in an Accept message.
HandleAccept(r, m) ==
    /\ pc[r] = "rloop"
    /\ m \in msgs
    /\ m.type = "Accept"
    /\ m.bal >= node[r].balMaxKnown
    /\ LET reply == [type |-> "AcceptReply", src |-> r,
                     bal |-> m.bal, slot |-> m.slot]
       IN /\ reply \notin msgs
          /\ node' = [node EXCEPT
                        ![r].balMaxKnown = m.bal,
                        ![r].insts[m.slot].voted = [bal |-> m.bal,
                                                    cmd |-> m.cmd]]
          /\ Send(reply)
    /\ UNCHANGED <<pc, observed>>

-----------------------------------------------------------------------------
(* Phase 3: Commit notice                                                  *)
-----------------------------------------------------------------------------

\* Leader learns a majority accepted slot s at its ballot; commits it.
HandleAcceptReplies(r, s) ==
    /\ pc[r] = "rloop"
    /\ IsLeader(r)
    /\ s \in Slots
    /\ node[r].insts[s].status = "Accepting"
    /\ Cardinality({q \in Replicas :
                      [type |-> "AcceptReply", src |-> q,
                       bal |-> node[r].balPrepared, slot |-> s] \in msgs})
         >= MajorityNum
    /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
    /\ Send([type |-> "CommitNotice", src |-> r, bal |-> node[r].balPrepared,
             slot |-> s, cmd |-> node[r].insts[s].cmd])
    /\ UNCHANGED <<pc, observed>>

\* Replica r learns that a slot has been committed.
HandleCommitNotice(r, m) ==
    /\ pc[r] = "rloop"
    /\ m \in msgs
    /\ m.type = "CommitNotice"
    /\ node[r].insts[m.slot].status # "Committed"
    /\ LET old == node[r].insts[m.slot]
       IN node' = [node EXCEPT ![r].insts[m.slot] =
                     [status |-> "Committed",
                      cmd    |-> m.cmd,
                      voted  |-> IF old.voted.bal < m.bal
                                   THEN [bal |-> m.bal, cmd |-> m.cmd]
                                   ELSE old.voted]]
    /\ UNCHANGED <<msgs, pc, observed>>

-----------------------------------------------------------------------------
(* Execution and client acknowledgement                                    *)
-----------------------------------------------------------------------------

\* Replica r executes the next committed slot. Duplicate log entries of
\* the same command are skipped. The first execution of a command
\* produces the client-observed acknowledgement.
Execute(r) ==
    LET s == node[r].commitUpTo + 1 IN
    /\ pc[r] = "rloop"
    /\ s \in Slots
    /\ node[r].insts[s].status = "Committed"
    /\ LET c      == node[r].insts[s].cmd
           dup    == c \in ExecutedCmds(r)
           newVal == IF c.type = "Write" /\ ~dup THEN c.val
                     ELSE node[r].kvalue
           ackVal == IF c.type = "Read" THEN node[r].kvalue ELSE c.val
       IN /\ node' = [node EXCEPT ![r].commitUpTo = s,
                                  ![r].kvalue = newVal]
          /\ IF c \in Commands /\ ~dup /\ c \notin Acked
               THEN observed' = Append(observed, AckEvent(c, ackVal))
               ELSE UNCHANGED observed
    /\ UNCHANGED <<msgs, pc>>

-----------------------------------------------------------------------------
(* Termination                                                             *)
-----------------------------------------------------------------------------

ReplicaTerminate(r) ==
    /\ pc[r] = "rloop"
    /\ Commands \subseteq ExecutedCmds(r)
    /\ pc' = [pc EXCEPT ![r] = "Done"]
    /\ UNCHANGED <<msgs, node, observed>>

\* Explicit stuttering once every replica has finished (avoids deadlock).
Terminating ==
    /\ \A r \in Replicas : pc[r] = "Done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next-state relation and specification                                   *)
-----------------------------------------------------------------------------

Client == \E c \in Commands : ClientRequest(c)

Replica(r) ==
    \/ \E b \in Ballots : Prepare(r, b)
    \/ \E m \in msgs : HandlePrepare(r, m)
    \/ BecomeLeader(r)
    \/ \E c \in Commands : TakeNewRequest(r, c)
    \/ \E s \in Slots : FillGap(r, s)
    \/ \E m \in msgs : HandleAccept(r, m)
    \/ \E s \in Slots : HandleAcceptReplies(r, s)
    \/ \E m \in msgs : HandleCommitNotice(r, m)
    \/ Execute(r)
    \/ ReplicaTerminate(r)

Next == \/ Client
        \/ \E r \in Replicas : Replica(r)
        \/ Terminating

Fairness == /\ WF_vars(Client)
            /\ \A r \in Replicas : WF_vars(Replica(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)
-----------------------------------------------------------------------------

\* All replicas agree on the command committed in each slot.
CommittedAgreement ==
    \A r1, r2 \in Replicas, s \in Slots :
        (/\ node[r1].insts[s].status = "Committed"
         /\ node[r2].insts[s].status = "Committed")
          => node[r1].insts[s].cmd = node[r2].insts[s].cmd

\* Every client request is issued at most once.
UniqueRequests ==
    \A i, j \in DOMAIN observed :
        (/\ observed[i].type = "Req"
         /\ observed[j].type = "Req"
         /\ observed[i].cmd = observed[j].cmd) => i = j

\* Every command is acknowledged at most once.
UniqueAcks ==
    \A i, j \in DOMAIN observed :
        (/\ observed[i].type = "Ack"
         /\ observed[j].type = "Ack"
         /\ observed[i].cmd = observed[j].cmd) => i = j

\* An acknowledgement only follows the corresponding request.
AckAfterRequest ==
    \A i \in DOMAIN observed :
        observed[i].type = "Ack" =>
            \E j \in 1..(i - 1) : observed[j] = ReqEvent(observed[i].cmd)

\* A read returns either the initial (null) value or a value whose write
\* request was issued before the read was acknowledged.
ReadReturnsWrittenValue ==
    \A i \in DOMAIN observed :
        (/\ observed[i].type = "Ack"
         /\ observed[i].cmd.type = "Read")
          => \/ observed[i].val = Nil
             \/ \E j \in 1..(i - 1) :
                   observed[j] = ReqEvent([type |-> "Write",
                                           val  |-> observed[i].val])

\* A read requested after some write was acknowledged cannot return the
\* initial null value.
ReadAfterAckedWriteNotNil ==
    \A i, j, k \in DOMAIN observed :
        (/\ i < j
         /\ observed[i].type = "Ack"
         /\ observed[i].cmd.type = "Write"
         /\ observed[j].type = "Req"
         /\ observed[j].cmd.type = "Read"
         /\ observed[k].type = "Ack"
         /\ observed[k].cmd = observed[j].cmd)
          => observed[k].val # Nil

SafetyInvariant ==
    /\ TypeOK
    /\ CommittedAgreement
    /\ UniqueRequests
    /\ UniqueAcks
    /\ AckAfterRequest
    /\ ReadReturnsWrittenValue
    /\ ReadAfterAckedWriteNotNil

-----------------------------------------------------------------------------
(* Liveness                                                                *)
-----------------------------------------------------------------------------

\* All replica processes eventually reach the "Done" control state.
Termination == <>(\A r \in Replicas : pc[r] = "Done")

=============================================================================
```