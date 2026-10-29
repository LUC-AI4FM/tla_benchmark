---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS NumReplicas, Writes, Reads, MaxBallot

ASSUME /\ NumReplicas \in Nat \ {0}
       /\ MaxBallot \in Nat
       /\ Writes \cap Reads = {}
       /\ "nil" \notin (Writes \cup Reads)

Replicas    == 0..(NumReplicas - 1)
Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
Slots       == 1..NumCommands
Ballots     == 0..MaxBallot
MajorityNum == (NumReplicas \div 2) + 1

BallotOwner(b) == b % NumReplicas

NullVote == [bal |-> 0, cmd |-> "nil"]
EmptyInst == [status |-> "Empty", cmd |-> "nil"]

ReqEvent(c)    == [type |-> "Req", cmd |-> c, val |-> "nil"]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

VARIABLES msgs,       \* monotonic set of all messages ever sent
          node,       \* per-replica state
          requested,  \* set of commands issued by clients so far
          observed,   \* sequence of client-observable events
          pc          \* control state of each replica process

vars == <<msgs, node, requested, observed, pc>>

ProcSet == Replicas

Range(s) == {s[i] : i \in DOMAIN s}

-----------------------------------------------------------------------------
Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |->
                 [leader      |-> "none",
                  balPrepared |-> 0,
                  balMaxKnown |-> 0,
                  insts       |-> [s \in Slots |-> EmptyInst],
                  voted       |-> [s \in Slots |-> NullVote],
                  commitUpTo  |-> 0,
                  kvalue      |-> "nil"]]
    /\ requested = {}
    /\ observed = << >>
    /\ pc = [r \in ProcSet |-> "rloop"]

Send(ms) == msgs' = msgs \cup ms

IsPreparedLeader(r) ==
    /\ node[r].balPrepared > 0
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ BallotOwner(node[r].balPrepared) = r

AckedCmds == {e.cmd : e \in {ev \in Range(observed) : ev.type = "Ack"}}

-----------------------------------------------------------------------------
(* Client issues a new request. *)
ClientRequest ==
    \E c \in Commands \ requested :
        /\ requested' = requested \cup {c}
        /\ observed' = Append(observed, ReqEvent(c))
        /\ UNCHANGED <<msgs, node, pc>>

(* Replica r starts a prepare phase with a fresh ballot it owns. *)
Prepare(r) ==
    /\ pc[r] = "rloop"
    /\ \E b \in Ballots :
         /\ b > node[r].balMaxKnown
         /\ BallotOwner(b) = r
         /\ b > 0
         /\ node[r]' = node[r]
         /\ node' = [node EXCEPT ![r].balMaxKnown = b, ![r].leader = r]
         /\ Send({[type |-> "Prepare", src |-> r, bal |-> b]})
    /\ UNCHANGED <<requested, observed, pc>>

(* Replica r handles a Prepare message. *)
HandlePrepare(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Prepare"
         /\ m.bal >= node[r].balMaxKnown
         /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal,
                                 ![r].leader = m.src]
         /\ Send({[type  |-> "PrepareReply",
                   src   |-> r,
                   bal   |-> m.bal,
                   voted |-> node[r].voted]})
    /\ UNCHANGED <<requested, observed, pc>>

(* Replica r becomes prepared leader after a majority of PrepareReplies. *)
BecomePrepared(r) ==
    /\ pc[r] = "rloop"
    /\ LET b == node[r].balMaxKnown
           replies == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
           MaxVote(s) ==
               CHOOSE v \in {m.voted[s] : m \in replies} \cup {NullVote} :
                   \A w \in {m.voted[s] : m \in replies} : w.bal <= v.bal
           newInsts ==
               [s \in Slots |->
                  IF node[r].insts[s].status = "Committed"
                  THEN node[r].insts[s]
                  ELSE IF MaxVote(s).bal > 0
                       THEN [status |-> "Accepting", cmd |-> MaxVote(s).cmd]
                       ELSE EmptyInst]
       IN /\ b > 0
          /\ BallotOwner(b) = r
          /\ node[r].balPrepared # b
          /\ \E Q \in SUBSET Replicas :
               /\ Cardinality(Q) >= MajorityNum
               /\ \A q \in Q : \E m \in replies : m.src = q
          /\ node' = [node EXCEPT ![r].balPrepared = b,
                                  ![r].leader = r,
                                  ![r].insts = newInsts]
          /\ Send({[type |-> "Accept", src |-> r, bal |-> b,
                    slot |-> s, cmd |-> newInsts[s].cmd] :
                     s \in {t \in Slots : newInsts[t].status = "Accepting"}})
    /\ UNCHANGED <<requested, observed, pc>>

(* Prepared leader r proposes a requested command in the first empty slot. *)
TakeRequest(r) ==
    /\ pc[r] = "rloop"
    /\ IsPreparedLeader(r)
    /\ \E c \in requested :
         /\ c \notin {node[r].insts[s].cmd : s \in Slots}
         /\ c \notin AckedCmds
         /\ \E s \in Slots :
              /\ node[r].insts[s].status = "Empty"
              /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
              /\ node' = [node EXCEPT ![r].insts[s] =
                                        [status |-> "Accepting", cmd |-> c]]
              /\ Send({[type |-> "Accept", src |-> r,
                        bal |-> node[r].balPrepared, slot |-> s, cmd |-> c]})
    /\ UNCHANGED <<requested, observed, pc>>

(* Replica r handles an Accept message. *)
HandleAccept(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Accept"
         /\ m.bal >= node[r].balMaxKnown
         /\ m.bal >= node[r].voted[m.slot].bal
         /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal,
                                 ![r].leader = m.src,
                                 ![r].voted[m.slot] =
                                     [bal |-> m.bal, cmd |-> m.cmd]]
         /\ Send({[type |-> "AcceptReply", src |-> r, bal |-> m.bal,
                   slot |-> m.slot, cmd |-> m.cmd]})
    /\ UNCHANGED <<requested, observed, pc>>

(* Prepared leader r commits a slot once a majority has accepted. *)
LeaderCommit(r) ==
    /\ pc[r] = "rloop"
    /\ IsPreparedLeader(r)
    /\ \E s \in Slots :
         /\ node[r].insts[s].status = "Accepting"
         /\ \E Q \in SUBSET Replicas :
              /\ Cardinality(Q) >= MajorityNum
              /\ \A q \in Q : \E m \in msgs :
                    /\ m.type = "AcceptReply"
                    /\ m.src = q
                    /\ m.bal = node[r].balPrepared
                    /\ m.slot = s
         /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
         /\ Send({[type |-> "CommitNotice", src |-> r, slot |-> s,
                   cmd |-> node[r].insts[s].cmd]})
    /\ UNCHANGED <<requested, observed, pc>>

(* Replica r learns a commit from a CommitNotice. *)
HandleCommit(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "CommitNotice"
         /\ node[r].insts[m.slot].status # "Committed"
         /\ node' = [node EXCEPT ![r].insts[m.slot] =
                                   [status |-> "Committed", cmd |-> m.cmd]]
    /\ UNCHANGED <<msgs, requested, observed, pc>>

(* Replica r executes the next committed slot in order; leader acks client. *)
Execute(r) ==
    /\ pc[r] = "rloop"
    /\ node[r].commitUpTo < NumCommands
    /\ LET s   == node[r].commitUpTo + 1
           c   == node[r].insts[s].cmd
           nv  == IF c \in Writes THEN c ELSE node[r].kvalue
       IN /\ node[r].insts[s].status = "Committed"
          /\ node' = [node EXCEPT ![r].commitUpTo = s,
                                  ![r].kvalue = nv]
          /\ IF IsPreparedLeader(r) /\ c \notin AckedCmds /\ c \in requested
               THEN observed' = Append(observed, AckEvent(c, nv))
               ELSE UNCHANGED observed
    /\ UNCHANGED <<msgs, requested, pc>>

(* Replica r terminates once its whole log is executed. *)
Finish(r) ==
    /\ pc[r] = "rloop"
    /\ node[r].commitUpTo = NumCommands
    /\ pc' = [pc EXCEPT ![r] = "Done"]
    /\ UNCHANGED <<msgs, node, requested, observed>>

Replica(r) ==
    \/ Prepare(r)
    \/ HandlePrepare(r)
    \/ BecomePrepared(r)
    \/ TakeRequest(r)
    \/ HandleAccept(r)
    \/ LeaderCommit(r)
    \/ HandleCommit(r)
    \/ Execute(r)
    \/ Finish(r)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A r \in ProcSet : pc[r] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ClientRequest
    \/ \E r \in Replicas : Replica(r)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ClientRequest)
    /\ \A r \in Replicas : WF_vars(Replica(r))

Termination == <>(\A r \in ProcSet : pc[r] = "Done")

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ requested \subseteq Commands
    /\ pc \in [ProcSet -> {"rloop", "Done"}]
    /\ \A r \in Replicas : node[r].commitUpTo \in 0..NumCommands

(* No two replicas commit different commands in the same slot. *)
Agreement ==
    \A r1, r2 \in Replicas : \A s \in Slots :
        (node[r1].insts[s].status = "Committed" /\
         node[r2].insts[s].status = "Committed")
           => node[r1].insts[s].cmd = node[r2].insts[s].cmd

(* Every acknowledgement is preceded by its request. *)
AckAfterReq ==
    \A i \in 1..Len(observed) :
        observed[i].type = "Ack" =>
            \E j \in 1..(i - 1) : observed[j] = ReqEvent(observed[i].cmd)

(* Each command is acknowledged at most once. *)
NoDuplicateAck ==
    \A i, j \in 1..Len(observed) :
        (i # j /\ observed[i].type = "Ack" /\ observed[j].type = "Ack")
            => observed[i].cmd # observed[j].cmd

(* Each command is requested at most once. *)
NoDuplicateReq ==
    \A i, j \in 1..Len(observed) :
        (i # j /\ observed[i].type = "Req" /\ observed[j].type = "Req")
            => observed[i].cmd # observed[j].cmd

(* Reads return either the initial value or a write that was requested
   before the read's acknowledgement. *)
ReadsReturnRequestedWrites ==
    \A i \in 1..Len(observed) :
        (observed[i].type = "Ack" /\ observed[i].cmd \in Reads) =>
            \/ observed[i].val = "nil"
            \/ \E j \in 1..(i - 1) : observed[j] = ReqEvent(observed[i].val)

(* Writes acknowledge with their own value. *)
WritesAckOwnValue ==
    \A i \in 1..Len(observed) :
        (observed[i].type = "Ack" /\ observed[i].cmd \in Writes) =>
            observed[i].val = observed[i].cmd

SafetyInv ==
    /\ TypeOK
    /\ Agreement
    /\ AckAfterReq
    /\ NoDuplicateAck
    /\ NoDuplicateReq
    /\ ReadsReturnRequestedWrites
    /\ WritesAckOwnValue

=============================================================================