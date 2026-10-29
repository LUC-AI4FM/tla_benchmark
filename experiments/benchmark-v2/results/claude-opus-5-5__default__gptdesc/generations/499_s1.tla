---------------------------- MODULE MultiPaxos_MC ----------------------------
EXTENDS FiniteSets, Sequences, Integers, TLC

CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME /\ Writes \cap Reads = {}
       /\ "nil" \notin (Writes \cup Reads)
       /\ "none" \notin Replicas
       /\ MaxBallot \in Nat
       /\ Replicas /= {}

VARIABLES msgs, node, pending, observed

vars == <<msgs, node, pending, observed>>

-----------------------------------------------------------------------------
(* Basic definitions *)

Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
Ballots     == 0..MaxBallot
Slots       == 1..NumCommands
Statuses    == {"Empty", "Accepting", "Committed"}

Range(f) == {f[i] : i \in DOMAIN f}

Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

Voted == [bal : Ballots \cup {-1}, cmd : Commands \cup {"nil"}]
NullVoted == [bal |-> -1, cmd |-> "nil"]

InstStates == [status : Statuses, cmd : Commands \cup {"nil"}, voted : Voted]
NullInst == [status |-> "Empty", cmd |-> "nil", voted |-> NullVoted]

NodeStates == [leader      : Replicas \cup {"none"},
               kvalue      : Writes \cup {"nil"},
               commitUpTo  : 0..NumCommands,
               balPrepared : Ballots \cup {-1},
               balMaxKnown : Ballots \cup {-1},
               insts       : [Slots -> InstStates]]

Messages ==
       [type : {"Prepare"}, src : Replicas, bal : Ballots]
  \cup [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
        voteds : [Slots -> Voted]]
  \cup [type : {"Accept"}, src : Replicas, bal : Ballots, slot : Slots,
        cmd : Commands]
  \cup [type : {"AcceptReply"}, src : Replicas, bal : Ballots, slot : Slots]
  \cup [type : {"CommitNotice"}, slot : Slots, cmd : Commands]

ClientEvents ==
       [type : {"Req"}, cmd : Commands]
  \cup [type : {"Ack"}, cmd : Commands, val : Writes \cup {"nil"}]

reqsMade == {observed[i].cmd :
               i \in {j \in 1..Len(observed) : observed[j].type = "Req"}}
acksRecv == {observed[i].cmd :
               i \in {j \in 1..Len(observed) : observed[j].type = "Ack"}}

terminated == /\ Len(pending) = 0
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |->
               [leader      |-> "none",
                kvalue      |-> "nil",
                commitUpTo  |-> 0,
                balPrepared |-> -1,
                balMaxKnown |-> -1,
                insts       |-> [s \in Slots |-> NullInst]]]
  /\ pending = <<>>
  /\ observed = <<>>

-----------------------------------------------------------------------------
(* Actions *)

ClientRequest ==
  \E c \in Commands \ reqsMade :
    /\ pending' = Append(pending, c)
    /\ observed' = Append(observed, [type |-> "Req", cmd |-> c])
    /\ UNCHANGED <<msgs, node>>

BecomeLeader(r) ==
  \E b \in Ballots :
    /\ b > node[r].balMaxKnown
    /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
    /\ node' = [node EXCEPT ![r].leader = r, ![r].balMaxKnown = b]
    /\ msgs' = msgs \cup {[type |-> "Prepare", src |-> r, bal |-> b]}
    /\ UNCHANGED <<pending, observed>>

HandlePrepare(r) ==
  \E m \in msgs :
    /\ m.type = "Prepare"
    /\ m.bal >= node[r].balMaxKnown
    /\ ~\E m2 \in msgs : /\ m2.type = "PrepareReply"
                         /\ m2.src = r
                         /\ m2.bal = m.bal
    /\ node' = [node EXCEPT ![r].leader = m.src, ![r].balMaxKnown = m.bal]
    /\ msgs' = msgs \cup
         {[type   |-> "PrepareReply",
           src    |-> r,
           bal    |-> m.bal,
           voteds |-> [s \in Slots |-> node[r].insts[s].voted]]}
    /\ UNCHANGED <<pending, observed>>

BecomePrepared(r) ==
  LET b == node[r].balMaxKnown
      ins == node[r].insts
  IN
  /\ node[r].leader = r
  /\ b >= 0
  /\ node[r].balPrepared /= b
  /\ \E Q \in Quorums :
       LET replies == {m \in msgs : /\ m.type = "PrepareReply"
                                    /\ m.bal = b
                                    /\ m.src \in Q}
           votesAt(s) == {m.voteds[s] : m \in replies}
           maxVote(s) == CHOOSE v \in votesAt(s) :
                           \A w \in votesAt(s) : w.bal =< v.bal
           newInsts == [s \in Slots |->
                          IF \/ ins[s].status = "Committed"
                             \/ maxVote(s).bal = -1
                          THEN ins[s]
                          ELSE [ins[s] EXCEPT !.status = "Accepting",
                                              !.cmd = maxVote(s).cmd]]
       IN
       /\ \A q \in Q : \E m \in replies : m.src = q
       /\ node' = [node EXCEPT ![r].balPrepared = b,
                               ![r].insts = newInsts]
       /\ msgs' = msgs \cup
            {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s,
              cmd |-> newInsts[s].cmd] :
               s \in {t \in Slots : newInsts[t].status = "Accepting"}}
  /\ UNCHANGED <<pending, observed>>

TakeNewRequest(r) ==
  LET b == node[r].balMaxKnown IN
  /\ node[r].leader = r
  /\ b >= 0
  /\ node[r].balPrepared = b
  /\ pending /= <<>>
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Empty"
       /\ \A t \in Slots : t < s => node[r].insts[t].status /= "Empty"
       /\ node' = [node EXCEPT ![r].insts[s].status = "Accepting",
                               ![r].insts[s].cmd = Head(pending)]
       /\ msgs' = msgs \cup
            {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s,
              cmd |-> Head(pending)]}
       /\ pending' = Tail(pending)
  /\ UNCHANGED observed

HandleAccept(r) ==
  \E m \in msgs :
    /\ m.type = "Accept"
    /\ m.bal >= node[r].balMaxKnown
    /\ ~\E m2 \in msgs : /\ m2.type = "AcceptReply"
                         /\ m2.src = r
                         /\ m2.bal = m.bal
                         /\ m2.slot = m.slot
    /\ node' = [node EXCEPT
                  ![r].leader = m.src,
                  ![r].balMaxKnown = m.bal,
                  ![r].insts[m.slot] =
                     IF node[r].insts[m.slot].status = "Committed"
                     THEN [node[r].insts[m.slot] EXCEPT
                             !.voted = [bal |-> m.bal, cmd |-> m.cmd]]
                     ELSE [status |-> "Accepting",
                           cmd    |-> m.cmd,
                           voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
    /\ msgs' = msgs \cup
         {[type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot]}
    /\ UNCHANGED <<pending, observed>>

BecomeCommitted(r) ==
  LET b == node[r].balMaxKnown IN
  /\ node[r].leader = r
  /\ b >= 0
  /\ node[r].balPrepared = b
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Accepting"
       /\ \E Q \in Quorums :
            \A q \in Q : \E m \in msgs : /\ m.type = "AcceptReply"
                                         /\ m.src = q
                                         /\ m.bal = b
                                         /\ m.slot = s
       /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
       /\ msgs' = msgs \cup
            {[type |-> "CommitNotice", slot |-> s,
              cmd |-> node[r].insts[s].cmd]}
  /\ UNCHANGED <<pending, observed>>

HandleCommitNotice(r) ==
  \E m \in msgs :
    /\ m.type = "CommitNotice"
    /\ node[r].insts[m.slot].status /= "Committed"
    /\ node' = [node EXCEPT ![r].insts[m.slot].status = "Committed",
                            ![r].insts[m.slot].cmd = m.cmd]
    /\ UNCHANGED <<msgs, pending, observed>>

Execute(r) ==
  LET s == node[r].commitUpTo + 1 IN
  /\ s \in Slots
  /\ node[r].insts[s].status = "Committed"
  /\ LET c    == node[r].insts[s].cmd
         newv == IF c \in Writes THEN c ELSE node[r].kvalue
     IN
     /\ node' = [node EXCEPT ![r].commitUpTo = s, ![r].kvalue = newv]
     /\ observed' = IF c \notin acksRecv
                    THEN Append(observed,
                                [type |-> "Ack", cmd |-> c, val |-> newv])
                    ELSE observed
  /\ UNCHANGED <<msgs, pending>>

Next ==
  \/ ClientRequest
  \/ \E r \in Replicas :
       \/ BecomeLeader(r)
       \/ HandlePrepare(r)
       \/ BecomePrepared(r)
       \/ TakeNewRequest(r)
       \/ HandleAccept(r)
       \/ BecomeCommitted(r)
       \/ HandleCommitNotice(r)
       \/ Execute(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* TLC-oriented helper definitions *)

ConstMaxBallot == 2

SymmetricPerms == Permutations(Replicas)
                  \cup Permutations(Writes)
                  \cup Permutations(Reads)

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
  /\ msgs \subseteq Messages
  /\ node \in [Replicas -> NodeStates]
  /\ Len(pending) =< NumCommands
  /\ Cardinality(Range(pending)) = Len(pending)
  /\ \A i \in 1..Len(pending) : pending[i] \in Commands
  /\ Len(observed) =< 2 * NumCommands
  /\ Cardinality(Range(observed)) = Len(observed)
  /\ \A i \in 1..Len(observed) : observed[i] \in ClientEvents
  /\ Cardinality(reqsMade) >= Cardinality(acksRecv)

-----------------------------------------------------------------------------
(* Linearizability over observed client events *)

Linearizability ==
  LET ReqPosOfCmd(c) ==
        CHOOSE i \in 1..Len(observed) : /\ observed[i].type = "Req"
                                        /\ observed[i].cmd = c
      AckPosOfCmd(c) ==
        CHOOSE i \in 1..Len(observed) : /\ observed[i].type = "Ack"
                                        /\ observed[i].cmd = c
      ResultOfCmd(c) == observed[AckPosOfCmd(c)].val
      OrderIdxOfCmd(order, c) ==
        CHOOSE j \in 1..NumCommands : order[j] = c
      LastWriteBefore(order, j) ==
        LET ws == {i \in 1..(j - 1) : order[i] \in Writes} IN
        IF ws = {} THEN "nil"
        ELSE order[CHOOSE i \in ws : \A i2 \in ws : i2 =< i]
      IsLinearOrder(order) ==
        /\ {order[j] : j \in 1..NumCommands} = Commands
        /\ \A j \in 1..NumCommands :
             ResultOfCmd(order[j]) =
               IF order[j] \in Writes THEN order[j]
                                      ELSE LastWriteBefore(order, j)
      ObeysRealTime(order) ==
        \A c1, c2 \in Commands :
          AckPosOfCmd(c1) < ReqPosOfCmd(c2)
            => OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2)
  IN
  terminated =>
    \E order \in [1..NumCommands -> Commands] :
      /\ IsLinearOrder(order)
      /\ ObeysRealTime(order)

-----------------------------------------------------------------------------
(* Top-level correctness theorems *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Linearizability

=============================================================================