---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC

CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME Cardinality(Replicas) >= 1
ASSUME Cardinality(Writes) >= 1
ASSUME MaxBallot >= 2

VARIABLES msgs, node, pending, observed

vars == <<msgs, node, pending, observed>>

-----------------------------------------------------------------------------
Commands == Writes \cup Reads

NumCommands == Cardinality(Commands)

Range(seq) == {seq[i] : i \in 1..Len(seq)}

Slots == 1..NumCommands

Ballots == 0..MaxBallot

CmdOrNil == Commands \cup {"nil"}

ReqEvent(c) == [type |-> "Req", cmd |-> c]

AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

ClientEvents ==
       [type : {"Req"}, cmd : Commands]
  \cup [type : {"Ack"}, cmd : Commands, val : Writes \cup {"nil"}]

VotedStates == [bal : Ballots, cmd : CmdOrNil]

InstStates == [status : {"Empty", "Accepting", "Committed"},
               cmd    : CmdOrNil,
               voted  : VotedStates]

NodeStates == [leader      : Replicas \cup {"none"},
               kvalue      : Writes \cup {"nil"},
               commitUpTo  : 0..NumCommands,
               balPrepared : Ballots,
               balMaxKnown : Ballots,
               insts       : [Slots -> InstStates]]

Messages ==
       [type : {"Prepare"}, src : Replicas, bal : Ballots]
  \cup [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
        voted : [Slots -> VotedStates]]
  \cup [type : {"Accept"}, src : Replicas, bal : Ballots, slot : Slots,
        cmd : CmdOrNil]
  \cup [type : {"AcceptReply"}, src : Replicas, bal : Ballots, slot : Slots]
  \cup [type : {"CommitNotice"}, src : Replicas, slot : Slots, cmd : CmdOrNil]

NullVote == [bal |-> 0, cmd |-> "nil"]

NullInst == [status |-> "Empty", cmd |-> "nil", voted |-> NullVote]

NullNode == [leader      |-> "none",
             kvalue      |-> "nil",
             commitUpTo  |-> 0,
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts       |-> [s \in Slots |-> NullInst]]

InitPending ==
  (CHOOSE ws \in [1..Cardinality(Writes) -> Writes] : Range(ws) = Writes)
  \o
  (CHOOSE rs \in [1..Cardinality(Reads) -> Reads] : Range(rs) = Reads)

reqsMade == {e.cmd : e \in {ev \in Range(observed) : ev.type = "Req"}}

acksRecv == {e.cmd : e \in {ev \in Range(observed) : ev.type = "Ack"}}

terminated ==
  /\ Len(pending) = 0
  /\ Cardinality(reqsMade) = NumCommands
  /\ Cardinality(acksRecv) = NumCommands

-----------------------------------------------------------------------------
Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |-> NullNode]
  /\ pending = InitPending
  /\ observed = <<>>

\* A replica becomes leader by broadcasting Prepare with a fresh ballot.
BecomeLeader(r) ==
  \E b \in 1..MaxBallot :
    /\ b > node[r].balMaxKnown
    /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ msgs' = msgs \cup {[type |-> "Prepare", src |-> r, bal |-> b]}
    /\ node' = [node EXCEPT ![r].leader = r,
                            ![r].balMaxKnown = b]
    /\ UNCHANGED <<pending, observed>>

\* A replica replies to a Prepare with its voted commands.
HandlePrepare(r) ==
  \E m \in msgs :
    /\ m.type = "Prepare"
    /\ m.bal >= node[r].balMaxKnown
    /\ ~ \E m2 \in msgs : /\ m2.type = "PrepareReply"
                          /\ m2.src = r
                          /\ m2.bal = m.bal
    /\ msgs' = msgs \cup {[type  |-> "PrepareReply",
                           src   |-> r,
                           bal   |-> m.bal,
                           voted |-> [s \in Slots |-> node[r].insts[s].voted]]}
    /\ node' = [node EXCEPT ![r].leader = m.src,
                            ![r].balMaxKnown = m.bal]
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers PrepareReplies from a majority and completes preparation.
HandlePrepareReplies(r) ==
  LET b == node[r].balMaxKnown
      prs == {m \in msgs : m.type = "PrepareReply" /\ m.bal = b}
      votesAt(s) == {v \in {m.voted[s] : m \in prs} : v.bal > 0}
      hasVote(s) == votesAt(s) # {}
      best(s) == CHOOSE v \in votesAt(s) :
                   \A v2 \in votesAt(s) : v2.bal <= v.bal
      maxSlot == IF \E s \in Slots : hasVote(s)
                 THEN CHOOSE s \in Slots :
                        /\ hasVote(s)
                        /\ \A s2 \in Slots : hasVote(s2) => s2 <= s
                 ELSE 0
      newCmd(s) == IF hasVote(s) THEN best(s).cmd ELSE "nil"
      toAccept == {s \in 1..maxSlot : node[r].insts[s].status # "Committed"}
      newInsts == [s \in Slots |->
                    IF node[r].insts[s].status = "Committed"
                    THEN node[r].insts[s]
                    ELSE IF s <= maxSlot
                         THEN [status |-> "Accepting",
                               cmd    |-> newCmd(s),
                               voted  |-> node[r].insts[s].voted]
                         ELSE [status |-> "Empty",
                               cmd    |-> "nil",
                               voted  |-> node[r].insts[s].voted]]
  IN /\ node[r].leader = r
     /\ b > 0
     /\ node[r].balPrepared # b
     /\ Cardinality(prs) * 2 > Cardinality(Replicas)
     /\ node' = [node EXCEPT ![r].balPrepared = b,
                             ![r].insts = newInsts]
     /\ msgs' = msgs \cup {[type |-> "Accept", src |-> r, bal |-> b,
                            slot |-> s, cmd |-> newCmd(s)] : s \in toAccept}
     /\ UNCHANGED <<pending, observed>>

\* A prepared leader takes a new client request into the first empty slot.
TakeNewRequest(r) ==
  /\ Len(pending) > 0
  /\ node[r].leader = r
  /\ node[r].balPrepared > 0
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Empty"
       /\ \A s2 \in Slots : s2 < s => node[r].insts[s2].status # "Empty"
       /\ LET c == Head(pending)
          IN /\ node' = [node EXCEPT ![r].insts[s] =
                           [status |-> "Accepting",
                            cmd    |-> c,
                            voted  |-> node[r].insts[s].voted]]
             /\ msgs' = msgs \cup {[type |-> "Accept", src |-> r,
                                    bal |-> node[r].balPrepared,
                                    slot |-> s, cmd |-> c]}
             /\ pending' = Tail(pending)
             /\ observed' = Append(observed, ReqEvent(c))

\* A replica votes on an Accept message.
HandleAccept(r) ==
  \E m \in msgs :
    /\ m.type = "Accept"
    /\ m.bal >= node[r].balMaxKnown
    /\ ~ \E m2 \in msgs : /\ m2.type = "AcceptReply"
                          /\ m2.src = r
                          /\ m2.bal = m.bal
                          /\ m2.slot = m.slot
    /\ LET inst == node[r].insts[m.slot]
           committed == inst.status = "Committed"
       IN node' = [node EXCEPT
                     ![r].leader = m.src,
                     ![r].balMaxKnown = m.bal,
                     ![r].insts[m.slot] =
                        [status |-> IF committed THEN "Committed" ELSE "Accepting",
                         cmd    |-> IF committed THEN inst.cmd ELSE m.cmd,
                         voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
    /\ msgs' = msgs \cup {[type |-> "AcceptReply", src |-> r,
                           bal |-> m.bal, slot |-> m.slot]}
    /\ UNCHANGED <<pending, observed>>

\* Leader commits the next slot upon majority AcceptReplies.
HandleAcceptReplies(r) ==
  LET b == node[r].balMaxKnown
      s == node[r].commitUpTo + 1
  IN /\ node[r].leader = r
     /\ b > 0
     /\ node[r].balPrepared = b
     /\ s \in Slots
     /\ node[r].insts[s].status = "Accepting"
     /\ Cardinality({m \in msgs : /\ m.type = "AcceptReply"
                                  /\ m.slot = s
                                  /\ m.bal = b}) * 2 > Cardinality(Replicas)
     /\ LET c == node[r].insts[s].cmd
            nv == IF c \in Writes THEN c ELSE node[r].kvalue
        IN /\ node' = [node EXCEPT ![r].insts[s].status = "Committed",
                                   ![r].commitUpTo = s,
                                   ![r].kvalue = nv]
           /\ msgs' = msgs \cup {[type |-> "CommitNotice", src |-> r,
                                  slot |-> s, cmd |-> c]}
           /\ observed' = IF c # "nil" /\ c \notin acksRecv
                          THEN Append(observed, AckEvent(c, nv))
                          ELSE observed
           /\ UNCHANGED pending

\* A replica learns about a committed slot (in order).
HandleCommitNotice(r) ==
  \E m \in msgs :
    /\ m.type = "CommitNotice"
    /\ m.slot = node[r].commitUpTo + 1
    /\ LET nv == IF m.cmd \in Writes THEN m.cmd ELSE node[r].kvalue
       IN node' = [node EXCEPT
                     ![r].insts[m.slot] =
                        [status |-> "Committed",
                         cmd    |-> m.cmd,
                         voted  |-> node[r].insts[m.slot].voted],
                     ![r].commitUpTo = m.slot,
                     ![r].kvalue = nv]
    /\ UNCHANGED <<msgs, pending, observed>>

Terminate ==
  /\ terminated
  /\ UNCHANGED vars

Next ==
  \/ \E r \in Replicas :
       \/ BecomeLeader(r)
       \/ HandlePrepare(r)
       \/ HandlePrepareReplies(r)
       \/ TakeNewRequest(r)
       \/ HandleAccept(r)
       \/ HandleAcceptReplies(r)
       \/ HandleCommitNotice(r)
  \/ Terminate

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
TypeOK ==
  /\ msgs \subseteq Messages
  /\ node \in [Replicas -> NodeStates]
  /\ Len(pending) <= NumCommands
  /\ Range(pending) \subseteq Commands
  /\ Range(observed) \subseteq ClientEvents

=============================================================================