---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME /\ Cardinality(Replicas) >= 1
       /\ Cardinality(Writes) >= 1
       /\ Writes \cap Reads = {}
       /\ MaxBallot \in Nat /\ MaxBallot >= 2

Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
MajorityNum == (Cardinality(Replicas) \div 2) + 1

Range(f) == {f[i] : i \in DOMAIN f}
Max(S)   == CHOOSE x \in S : \A y \in S : y <= x

Ballots  == 1..MaxBallot
Slots    == 1..NumCommands
Statuses == {"Empty", "Accepting", "Committed"}

Votes == [bal: {0} \cup Ballots, cmd: {"nil"} \cup Commands]

InstStates == [status: Statuses, cmd: {"nil"} \cup Commands, voted: Votes]

NullInst == [status |-> "Empty", cmd |-> "nil",
             voted  |-> [bal |-> 0, cmd |-> "nil"]]

NodeStates == [leader:      {"none"} \cup Replicas,
               kvalue:      {"nil"} \cup Writes,
               commitUpTo:  {0} \cup Slots,
               balPrepared: {0} \cup Ballots,
               balMaxKnown: {0} \cup Ballots,
               insts:       [Slots -> InstStates]]

NullNode == [leader      |-> "none",
             kvalue      |-> "nil",
             commitUpTo  |-> 0,
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts       |-> [s \in Slots |-> NullInst]]

Messages ==      [type: {"Prepare"}, src: Replicas, bal: Ballots]
            \cup [type: {"PrepareReply"}, src: Replicas, bal: Ballots,
                  voted: [Slots -> Votes]]
            \cup [type: {"Accept"}, src: Replicas, bal: Ballots,
                  slot: Slots, cmd: Commands]
            \cup [type: {"AcceptReply"}, src: Replicas, bal: Ballots,
                  slot: Slots]
            \cup [type: {"CommitNotice"}, slot: Slots, cmd: Commands]

ClientEvents ==      [type: {"Req"}, cmd: Commands]
                \cup [type: {"Ack"}, cmd: Commands, val: {"nil"} \cup Writes]

VARIABLES msgs, node, pending, observed

vars == <<msgs, node, pending, observed>>

reqsMade == {e.cmd : e \in {x \in Range(observed) : x.type = "Req"}}
acksRecv == {e.cmd : e \in {x \in Range(observed) : x.type = "Ack"}}

terminated == /\ Len(observed) = 2 * NumCommands
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

TypeOK == /\ msgs \subseteq Messages
          /\ node \in [Replicas -> NodeStates]
          /\ pending \subseteq Commands
          /\ observed \in Seq(ClientEvents)

Init == /\ msgs = {}
        /\ node = [r \in Replicas |-> NullNode]
        /\ pending = Commands
        /\ observed = <<>>

IsLeader(r) == /\ node[r].leader = r
               /\ node[r].balPrepared > 0
               /\ node[r].balPrepared = node[r].balMaxKnown

-----------------------------------------------------------------------------
(* Phase 1: leader election *)

BecomeLeader(r) ==
  \E b \in Ballots :
    /\ b > node[r].balMaxKnown
    /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ node' = [node EXCEPT ![r].leader = r, ![r].balMaxKnown = b]
    /\ msgs' = msgs \cup {[type |-> "Prepare", src |-> r, bal |-> b]}
    /\ UNCHANGED <<pending, observed>>

HandlePrepare(s) ==
  \E m \in msgs :
    /\ m.type = "Prepare"
    /\ \/ m.bal > node[s].balMaxKnown
       \/ m.bal = node[s].balMaxKnown /\ node[s].leader = m.src
    /\ node' = [node EXCEPT ![s].leader = m.src, ![s].balMaxKnown = m.bal]
    /\ msgs' = msgs \cup
         {[type  |-> "PrepareReply", src |-> s, bal |-> m.bal,
           voted |-> [t \in Slots |-> node[s].insts[t].voted]]}
    /\ UNCHANGED <<pending, observed>>

HandlePrepareReplies(r) ==
  LET b       == node[r].balMaxKnown
      replies == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
      Recovered(t) ==
        LET vs == {m.voted[t] : m \in replies}
            mb == Max({v.bal : v \in vs})
        IN IF mb = 0 THEN "nil" ELSE (CHOOSE v \in vs : v.bal = mb).cmd
      newInsts ==
        [t \in Slots |->
           IF node[r].insts[t].status = "Committed" THEN node[r].insts[t]
           ELSE IF Recovered(t) = "nil" THEN NullInst
           ELSE [status |-> "Accepting", cmd |-> Recovered(t),
                 voted  |-> [bal |-> b, cmd |-> Recovered(t)]]]
      accSlots == {t \in Slots : newInsts[t].status = "Accepting"}
  IN
  /\ node[r].leader = r
  /\ b > 0
  /\ node[r].balPrepared # b
  /\ Cardinality({m.src : m \in replies}) >= MajorityNum
  /\ node' = [node EXCEPT ![r].balPrepared = b, ![r].insts = newInsts]
  /\ msgs' = msgs \cup
       UNION {{[type |-> "Accept", src |-> r, bal |-> b, slot |-> t,
                cmd |-> newInsts[t].cmd],
               [type |-> "AcceptReply", src |-> r, bal |-> b, slot |-> t]}
              : t \in accSlots}
  /\ UNCHANGED <<pending, observed>>

-----------------------------------------------------------------------------
(* Phase 2: log replication *)

Propose(r) ==
  /\ IsLeader(r)
  /\ \E c \in pending, s \in Slots :
       /\ node[r].insts[s].status = "Empty"
       /\ \A t \in 1..(s-1) : node[r].insts[t].status # "Empty"
       /\ LET b == node[r].balPrepared IN
          /\ node' = [node EXCEPT ![r].insts[s] =
                        [status |-> "Accepting", cmd |-> c,
                         voted  |-> [bal |-> b, cmd |-> c]]]
          /\ msgs' = msgs \cup
               {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c],
                [type |-> "AcceptReply", src |-> r, bal |-> b, slot |-> s]}
       /\ pending' = pending \ {c}
       /\ observed' = Append(observed, [type |-> "Req", cmd |-> c])

HandleAccept(s) ==
  \E m \in msgs :
    /\ m.type = "Accept"
    /\ m.src # s
    /\ m.bal >= node[s].balMaxKnown
    /\ node' = [node EXCEPT
                  ![s].leader = m.src,
                  ![s].balMaxKnown = m.bal,
                  ![s].insts[m.slot] =
                     IF node[s].insts[m.slot].status = "Committed"
                     THEN [node[s].insts[m.slot] EXCEPT
                             !.voted = [bal |-> m.bal, cmd |-> m.cmd]]
                     ELSE [status |-> "Accepting", cmd |-> m.cmd,
                           voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
    /\ msgs' = msgs \cup
         {[type |-> "AcceptReply", src |-> s, bal |-> m.bal, slot |-> m.slot]}
    /\ UNCHANGED <<pending, observed>>

HandleAcceptReplies(r) ==
  /\ IsLeader(r)
  /\ \E t \in Slots :
       /\ node[r].insts[t].status = "Accepting"
       /\ Cardinality({m.src : m \in {x \in msgs : /\ x.type = "AcceptReply"
                                                  /\ x.bal = node[r].balPrepared
                                                  /\ x.slot = t}})
            >= MajorityNum
       /\ node' = [node EXCEPT ![r].insts[t].status = "Committed"]
       /\ msgs' = msgs \cup
            {[type |-> "CommitNotice", slot |-> t,
              cmd |-> node[r].insts[t].cmd]}
  /\ UNCHANGED <<pending, observed>>

-----------------------------------------------------------------------------
(* Phase 3: commit notification and execution *)

HandleCommitNotice(s) ==
  \E m \in msgs :
    /\ m.type = "CommitNotice"
    /\ node[s].insts[m.slot].status # "Committed"
    /\ node' = [node EXCEPT ![s].insts[m.slot].status = "Committed",
                            ![s].insts[m.slot].cmd = m.cmd]
    /\ UNCHANGED <<msgs, pending, observed>>

ExecuteNext(r) ==
  LET s == node[r].commitUpTo + 1 IN
  /\ s <= NumCommands
  /\ node[r].insts[s].status = "Committed"
  /\ LET c   == node[r].insts[s].cmd
         old == node[r].kvalue
     IN /\ node' = [node EXCEPT ![r].commitUpTo = s,
                                ![r].kvalue = IF c \in Writes THEN c ELSE old]
        /\ observed' = IF c \notin acksRecv
                       THEN Append(observed, [type |-> "Ack", cmd |-> c, val |-> old])
                       ELSE observed
  /\ UNCHANGED <<msgs, pending>>

-----------------------------------------------------------------------------

Terminating == terminated /\ UNCHANGED vars

Next == \/ \E r \in Replicas :
             \/ BecomeLeader(r)
             \/ HandlePrepare(r)
             \/ HandlePrepareReplies(r)
             \/ Propose(r)
             \/ HandleAccept(r)
             \/ HandleAcceptReplies(r)
             \/ HandleCommitNotice(r)
             \/ ExecuteNext(r)
        \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

ConsensusSafety ==
  \A r1, r2 \in Replicas, t \in Slots :
    (/\ node[r1].insts[t].status = "Committed"
     /\ node[r2].insts[t].status = "Committed")
      => node[r1].insts[t].cmd = node[r2].insts[t].cmd

Orders == {f \in [1..NumCommands -> Commands] : Range(f) = Commands}

Linearizability ==
  terminated =>
    LET ReqPos(c) == CHOOSE i \in DOMAIN observed :
                        observed[i].type = "Req" /\ observed[i].cmd = c
        AckPos(c) == CHOOSE i \in DOMAIN observed :
                        observed[i].type = "Ack" /\ observed[i].cmd = c
        PrevWrite(ord, i) ==
          LET ws == {j \in 1..(i-1) : ord[j] \in Writes}
          IN IF ws = {} THEN "nil" ELSE ord[Max(ws)]
    IN \E ord \in Orders :
         /\ \A i, j \in 1..NumCommands :
              AckPos(ord[j]) < ReqPos(ord[i]) => j < i
         /\ \A i \in 1..NumCommands :
              observed[AckPos(ord[i])].val = PrevWrite(ord, i)

NoDeadlockBeforeDone == []( ~terminated => ENABLED (Next /\ ~Terminating) )

=============================================================================