---------------------------- MODULE MultiPaxos ----------------------------
(***************************************************************************)
(* MultiPaxos state machine replication on a single key, with write and   *)
(* read commands. The network is a monotonically growing set of sent      *)
(* messages, so messages may be delayed, duplicated, or lost (never       *)
(* consumed). The algorithm uses Prepare, Accept and CommitNotice phases. *)
(* Client-observable behavior is recorded in the "observed" sequence of   *)
(* request and acknowledgement events.                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumReplicas,   \* number of replicas, identified as 0..NumReplicas-1
          Writes,        \* set of write commands (a write writes its own id)
          Reads,         \* set of read commands
          MaxBallot      \* largest ballot number usable

ASSUME NumReplicas \in Nat \ {0}
ASSUME MaxBallot \in Nat
ASSUME Writes \cap Reads = {}

Replicas    == 0..(NumReplicas - 1)
Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
Slots       == 1..NumCommands
Ballots     == 1..MaxBallot
BallotsOf(r) == {b \in Ballots : b % NumReplicas = r}
MajorityNum == (NumReplicas \div 2) + 1

NullCmd  == "nil"
NoLeader == -1
NullVote == [bal |-> 0, cmd |-> NullCmd]

Statuses == {"Empty", "Preparing", "Accepting", "Committed"}

InitInst == [status |-> "Empty", cmd |-> NullCmd, voted |-> NullVote]

InitNode == [leader      |-> NoLeader,
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts       |-> [s \in Slots |-> InitInst],
             executed    |-> 0,
             kvalue      |-> NullCmd]

VARIABLES msgs,      \* set of all messages ever sent
          node,      \* per-replica state
          pending,   \* client requests not yet taken by a leader
          observed,  \* client-observed sequence of req/ack events
          pc         \* per-replica control state

vars == <<msgs, node, pending, observed, pc>>

ReqEvent(c)    == [type |-> "req", cmd |-> c, val |-> NullCmd]
AckEvent(c, v) == [type |-> "ack", cmd |-> c, val |-> v]

Requested(c) == \E i \in 1..Len(observed) :
                    observed[i].type = "req" /\ observed[i].cmd = c
Acked(c)     == \E i \in 1..Len(observed) :
                    observed[i].type = "ack" /\ observed[i].cmd = c

Send(m)     == msgs' = msgs \cup {m}
SendSet(ms) == msgs' = msgs \cup ms

-----------------------------------------------------------------------------
TypeOK ==
    /\ pending \subseteq Commands
    /\ pc \in [Replicas -> {"rloop", "Done"}]
    /\ \A r \in Replicas :
         /\ node[r].leader \in Replicas \cup {NoLeader}
         /\ node[r].balPrepared \in 0..MaxBallot
         /\ node[r].balMaxKnown \in 0..MaxBallot
         /\ node[r].executed \in 0..NumCommands
         /\ node[r].kvalue \in Writes \cup {NullCmd}
         /\ \A s \in Slots :
              /\ node[r].insts[s].status \in Statuses
              /\ node[r].insts[s].cmd \in Commands \cup {NullCmd}
              /\ node[r].insts[s].voted.bal \in 0..MaxBallot
              /\ node[r].insts[s].voted.cmd \in Commands \cup {NullCmd}
    /\ \A i \in 1..Len(observed) :
         /\ observed[i].type \in {"req", "ack"}
         /\ observed[i].cmd \in Commands

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |-> InitNode]
    /\ pending = {}
    /\ observed = <<>>
    /\ pc = [r \in Replicas |-> "rloop"]

(* A client issues a new request. *)
ClientRequest(c) ==
    /\ ~Requested(c)
    /\ observed' = Append(observed, ReqEvent(c))
    /\ pending' = pending \cup {c}
    /\ UNCHANGED <<msgs, node, pc>>

(* Replica r starts the prepare phase with its own ballot b. *)
PrepareBegin(r, b) ==
    /\ pc[r] = "rloop"
    /\ b > node[r].balMaxKnown
    /\ node' = [node EXCEPT
                 ![r].leader = r,
                 ![r].balPrepared = 0,
                 ![r].balMaxKnown = b,
                 ![r].insts = [s \in Slots |->
                     IF node[r].insts[s].status \in {"Preparing", "Accepting"}
                       THEN [node[r].insts[s] EXCEPT !.status = "Preparing"]
                       ELSE node[r].insts[s]]]
    /\ Send([type |-> "Prepare", src |-> r, bal |-> b])
    /\ UNCHANGED <<pending, observed, pc>>

(* Replica r handles a Prepare message and replies with its votes. *)
HandlePrepare(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Prepare"
         /\ m.bal >= node[r].balMaxKnown
         /\ ~\E m2 \in msgs : /\ m2.type = "PrepareReply"
                              /\ m2.src = r
                              /\ m2.bal = m.bal
         /\ node' = [node EXCEPT
                      ![r].leader = m.src,
                      ![r].balMaxKnown = m.bal,
                      ![r].balPrepared = IF m.src = r
                                           THEN node[r].balPrepared ELSE 0]
         /\ Send([type  |-> "PrepareReply",
                  src   |-> r,
                  bal   |-> m.bal,
                  voted |-> [s \in Slots |-> node[r].insts[s].voted]])
    /\ UNCHANGED <<pending, observed, pc>>

(* Leader r collects a majority of PrepareReplies and becomes prepared. *)
HandlePrepareReplies(r) ==
    LET b       == node[r].balMaxKnown
        replies == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
        votes(s)   == {m.voted[s] : m \in replies}
        maxVote(s) == CHOOSE v \in votes(s) :
                          \A w \in votes(s) : w.bal <= v.bal
        newInst(s) ==
            IF node[r].insts[s].status = "Committed"
              THEN node[r].insts[s]
              ELSE IF maxVote(s).bal > 0
                     THEN [node[r].insts[s] EXCEPT !.status = "Accepting",
                                                   !.cmd = maxVote(s).cmd]
                     ELSE [node[r].insts[s] EXCEPT !.status = "Empty",
                                                   !.cmd = NullCmd]
        newInsts == [s \in Slots |-> newInst(s)]
        toAccept == {s \in Slots : newInsts[s].status = "Accepting"}
    IN
    /\ pc[r] = "rloop"
    /\ node[r].leader = r
    /\ node[r].balPrepared = 0
    /\ b > 0
    /\ Cardinality({m.src : m \in replies}) >= MajorityNum
    /\ node' = [node EXCEPT ![r].insts = newInsts,
                            ![r].balPrepared = b]
    /\ SendSet({[type |-> "Accept", src |-> r, bal |-> b,
                 slot |-> s, cmd |-> newInsts[s].cmd] : s \in toAccept})
    /\ UNCHANGED <<pending, observed, pc>>

(* Prepared leader r places a pending client command into the first empty slot. *)
TakeNewRequest(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared = b
    /\ \E c \in pending, s \in Slots :
         /\ node[r].insts[s].status = "Empty"
         /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
         /\ node' = [node EXCEPT ![r].insts[s].status = "Accepting",
                                 ![r].insts[s].cmd = c]
         /\ pending' = pending \ {c}
         /\ Send([type |-> "Accept", src |-> r, bal |-> b,
                  slot |-> s, cmd |-> c])
    /\ UNCHANGED <<observed, pc>>

(* Replica r handles an Accept message and votes. *)
HandleAccept(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Accept"
         /\ m.bal >= node[r].balMaxKnown
         /\ ~\E m2 \in msgs : /\ m2.type = "AcceptReply"
                              /\ m2.src = r
                              /\ m2.bal = m.bal
                              /\ m2.slot = m.slot
         /\ node' = [node EXCEPT
                      ![r].leader = m.src,
                      ![r].balMaxKnown = m.bal,
                      ![r].balPrepared = IF m.src = r
                                           THEN node[r].balPrepared ELSE 0,
                      ![r].insts[m.slot] =
                          [status |-> IF node[r].insts[m.slot].status = "Committed"
                                        THEN "Committed" ELSE "Accepting",
                           cmd    |-> m.cmd,
                           voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
         /\ Send([type |-> "AcceptReply", src |-> r,
                  bal |-> m.bal, slot |-> m.slot])
    /\ UNCHANGED <<pending, observed, pc>>

(* Leader r commits a slot once a majority accepted it, and sends a CommitNotice. *)
HandleAcceptReplies(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared = b
    /\ \E s \in Slots :
         /\ node[r].insts[s].status = "Accepting"
         /\ node[r].insts[s].voted.bal = b
         /\ Cardinality({m.src : m \in {m2 \in msgs :
                              /\ m2.type = "AcceptReply"
                              /\ m2.bal = b
                              /\ m2.slot = s}}) >= MajorityNum
         /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
         /\ Send([type |-> "CommitNotice", src |-> r, bal |-> b,
                  slot |-> s, cmd |-> node[r].insts[s].cmd])
    /\ UNCHANGED <<pending, observed, pc>>

(* Replica r learns a committed slot from a CommitNotice. *)
HandleCommitNotice(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "CommitNotice"
         /\ node[r].insts[m.slot].status # "Committed"
         /\ node' = [node EXCEPT ![r].insts[m.slot].status = "Committed",
                                 ![r].insts[m.slot].cmd = m.cmd]
    /\ UNCHANGED <<msgs, pending, observed, pc>>

(* Replica r executes the next committed slot in log order; the leader acks. *)
Execute(r) ==
    LET s == node[r].executed + 1 IN
    /\ pc[r] = "rloop"
    /\ s \in Slots
    /\ node[r].insts[s].status = "Committed"
    /\ LET c     == node[r].insts[s].cmd
           newkv == IF c \in Writes THEN c ELSE node[r].kvalue
       IN
       /\ node' = [node EXCEPT ![r].executed = s,
                               ![r].kvalue = newkv]
       /\ observed' = IF node[r].leader = r /\ ~Acked(c)
                        THEN Append(observed, AckEvent(c, newkv))
                        ELSE observed
    /\ UNCHANGED <<msgs, pending, pc>>

(* Replica r terminates once its whole log is committed and executed. *)
Finish(r) ==
    /\ pc[r] = "rloop"
    /\ node[r].executed = NumCommands
    /\ pc' = [pc EXCEPT ![r] = "Done"]
    /\ UNCHANGED <<msgs, node, pending, observed>>

(* Explicit stuttering after termination to avoid deadlock. *)
Terminating ==
    /\ \A r \in Replicas : pc[r] = "Done"
    /\ UNCHANGED vars

Replica(r) ==
    \/ \E b \in BallotsOf(r) : PrepareBegin(r, b)
    \/ HandlePrepare(r)
    \/ HandlePrepareReplies(r)
    \/ TakeNewRequest(r)
    \/ HandleAccept(r)
    \/ HandleAcceptReplies(r)
    \/ HandleCommitNotice(r)
    \/ Execute(r)
    \/ Finish(r)

Next ==
    \/ \E c \in Commands : ClientRequest(c)
    \/ \E r \in Replicas : Replica(r)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

CommitSafety ==
    \A r1, r2 \in Replicas, s \in Slots :
        (/\ node[r1].insts[s].status = "Committed"
         /\ node[r2].insts[s].status = "Committed")
        => node[r1].insts[s].cmd = node[r2].insts[s].cmd

AcksHaveRequests ==
    \A i \in 1..Len(observed) :
        observed[i].type = "ack" =>
            \E j \in 1..(i - 1) : observed[j] = ReqEvent(observed[i].cmd)

AckOnce ==
    \A i, j \in 1..Len(observed) :
        (/\ observed[i].type = "ack"
         /\ observed[j].type = "ack"
         /\ observed[i].cmd = observed[j].cmd) => i = j

WriteAckValues ==
    \A i \in 1..Len(observed) :
        (observed[i].type = "ack" /\ observed[i].cmd \in Writes)
            => observed[i].val = observed[i].cmd

ReadValuesValid ==
    \A i \in 1..Len(observed) :
        (observed[i].type = "ack" /\ observed[i].cmd \in Reads) =>
            \/ observed[i].val = NullCmd
            \/ /\ observed[i].val \in Writes
               /\ \E j \in 1..(i - 1) : observed[j] = ReqEvent(observed[i].val)

ReadsSeeAckedWrites ==
    \A i, j, k \in 1..Len(observed) :
        (/\ observed[j].type = "ack"
         /\ observed[j].cmd \in Writes
         /\ observed[k].type = "req"
         /\ observed[k].cmd \in Reads
         /\ j < k
         /\ observed[i].type = "ack"
         /\ observed[i].cmd = observed[k].cmd)
            => observed[i].val # NullCmd

Safety ==
    /\ CommitSafety
    /\ AcksHaveRequests
    /\ AckOnce
    /\ WriteAckValues
    /\ ReadValuesValid
    /\ ReadsSeeAckedWrites

(* Liveness property *)
Termination == <>(\A r \in Replicas : pc[r] = "Done")

=============================================================================