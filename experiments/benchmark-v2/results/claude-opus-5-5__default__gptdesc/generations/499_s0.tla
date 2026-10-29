---------------------------- MODULE MCMultiPaxos ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Self-contained MultiPaxos model plus TLC-oriented helper definitions:   *)
(* symmetry permutations, a constant ballot bound, a type invariant, and   *)
(* a linearizability condition checked over observed client events.       *)
(***************************************************************************)

CONSTANTS Replicas,     \* set of replica nodes
          Writes,       \* set of write values (one Put command per value)
          Reads,        \* set of read ids (one Get command per id)
          MaxBallot     \* upper bound on ballot numbers

ASSUME /\ Replicas /= {}
       /\ IsFiniteSet(Replicas)
       /\ IsFiniteSet(Writes)
       /\ IsFiniteSet(Reads)
       /\ MaxBallot \in Nat /\ MaxBallot >= 1

VARIABLES msgs,      \* set of messages ever sent
          node,      \* replica node states
          pending,   \* sequence of client commands yet to be submitted
          observed   \* sequence of observed client events (Req / Ack)

vars == <<msgs, node, pending, observed>>

-----------------------------------------------------------------------------
(* TLC helper definitions *)

ReplicaPerms   == Permutations(Replicas)
WritePerms     == Permutations(Writes)
ReadPerms      == Permutations(Reads)
SymmetricPerms == WritePerms \cup ReadPerms

ConstMaxBallot == 2

-----------------------------------------------------------------------------
(* Basic definitions *)

Commands == [type: {"Put"}, val: Writes] \cup [type: {"Get"}, val: Reads]
NullCmd  == [type |-> "Nop", val |-> "none"]
NoValue  == "nil"

NumCommands == Cardinality(Writes) + Cardinality(Reads)
Slots       == 1..NumCommands
Ballots     == 1..MaxBallot
MajorityNum == (Cardinality(Replicas) \div 2) + 1

Statuses == {"Empty", "Preparing", "Accepting", "Committed"}

ReplicaIdx == CHOOSE f \in [Replicas -> 1..Cardinality(Replicas)] :
                \A a, b \in Replicas : a /= b => f[a] /= f[b]

Owns(r, b) == ((b - 1) % Cardinality(Replicas)) + 1 = ReplicaIdx[r]

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

VotedStates == [bal: 0..MaxBallot, cmd: Commands \cup {NullCmd}]

InstStates == [status: Statuses,
               cmd: Commands \cup {NullCmd},
               voted: VotedStates,
               voters: SUBSET Replicas]

NullInst == [status |-> "Empty", cmd |-> NullCmd,
             voted |-> [bal |-> 0, cmd |-> NullCmd], voters |-> {}]

NodeStates == [leader: Replicas \cup {"none"},
               balPrepared: 0..MaxBallot,
               balMaxKnown: 0..MaxBallot,
               prepVoters: SUBSET Replicas,
               insts: [Slots -> InstStates]]

Messages ==
       [type: {"Prepare"}, src: Replicas, bal: Ballots]
  \cup [type: {"PrepareReply"}, src: Replicas, dst: Replicas, bal: Ballots,
        voteds: [Slots -> VotedStates]]
  \cup [type: {"Accept"}, src: Replicas, bal: Ballots, slot: Slots,
        cmd: Commands]
  \cup [type: {"AcceptReply"}, src: Replicas, dst: Replicas, bal: Ballots,
        slot: Slots]

ClientEvents ==
       [type: {"Req"}, cmd: Commands]
  \cup [type: {"Ack"}, cmd: Commands, val: Writes \cup {NoValue}]

ReqEvent(c)    == [type |-> "Req", cmd |-> c]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

Orders == {seq \in [1..NumCommands -> Commands] :
             \A i, j \in 1..NumCommands : i /= j => seq[i] /= seq[j]}

ReqPositions == {i \in 1..Len(observed) : observed[i].type = "Req"}
AckPositions == {i \in 1..Len(observed) : observed[i].type = "Ack"}

Acked(c) == \E i \in AckPositions : observed[i].cmd = c

Terminated == /\ pending = <<>>
              /\ Cardinality(AckPositions) = NumCommands

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |->
               [leader |-> "none", balPrepared |-> 0, balMaxKnown |-> 0,
                prepVoters |-> {}, insts |-> [s \in Slots |-> NullInst]]]
  /\ pending \in Orders
  /\ observed = <<>>

-----------------------------------------------------------------------------
(* Actions *)

BecomeLeader(r) ==
  \E b \in Ballots :
    /\ b > node[r].balMaxKnown
    /\ Owns(r, b)
    /\ node' = [node EXCEPT
                  ![r].leader = r,
                  ![r].balMaxKnown = b,
                  ![r].prepVoters = {r},
                  ![r].insts = [s \in Slots |->
                      IF node[r].insts[s].status = "Accepting"
                        THEN [node[r].insts[s] EXCEPT !.status = "Preparing"]
                        ELSE node[r].insts[s]]]
    /\ msgs' = msgs \cup {[type |-> "Prepare", src |-> r, bal |-> b]}
    /\ UNCHANGED <<pending, observed>>

HandlePrepare(r) ==
  \E m \in msgs :
    /\ m.type = "Prepare"
    /\ m.src /= r
    /\ m.bal > node[r].balMaxKnown
    /\ node' = [node EXCEPT
                  ![r].leader = m.src,
                  ![r].balMaxKnown = m.bal,
                  ![r].prepVoters = {}]
    /\ msgs' = msgs \cup
         {[type |-> "PrepareReply", src |-> r, dst |-> m.src, bal |-> m.bal,
           voteds |-> [s \in Slots |-> node[r].insts[s].voted]]}
    /\ UNCHANGED <<pending, observed>>

HandlePrepareReply(r) ==
  \E m \in msgs :
    /\ m.type = "PrepareReply"
    /\ m.dst = r
    /\ node[r].leader = r
    /\ m.bal = node[r].balMaxKnown
    /\ node[r].balPrepared < m.bal
    /\ m.src \notin node[r].prepVoters
    /\ node' = [node EXCEPT
                  ![r].prepVoters = @ \cup {m.src},
                  ![r].insts = [s \in Slots |->
                      IF /\ node[r].insts[s].status /= "Committed"
                         /\ m.voteds[s].bal > node[r].insts[s].voted.bal
                        THEN [node[r].insts[s] EXCEPT
                                !.status = "Preparing",
                                !.cmd = m.voteds[s].cmd,
                                !.voted = m.voteds[s]]
                        ELSE node[r].insts[s]]]
    /\ UNCHANGED <<msgs, pending, observed>>

FinishPrepare(r) ==
  /\ node[r].leader = r
  /\ node[r].balPrepared < node[r].balMaxKnown
  /\ Cardinality(node[r].prepVoters) >= MajorityNum
  /\ LET b       == node[r].balMaxKnown
         reSlots == {s \in Slots : node[r].insts[s].status = "Preparing"}
     IN /\ node' = [node EXCEPT
                      ![r].balPrepared = b,
                      ![r].insts = [s \in Slots |->
                          IF s \in reSlots
                            THEN [node[r].insts[s] EXCEPT
                                    !.status = "Accepting",
                                    !.voted = [bal |-> b,
                                               cmd |-> node[r].insts[s].cmd],
                                    !.voters = {r}]
                            ELSE node[r].insts[s]]]
        /\ msgs' = msgs \cup
             {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s,
               cmd |-> node[r].insts[s].cmd] : s \in reSlots}
  /\ UNCHANGED <<pending, observed>>

TakeNewRequest(r) ==
  /\ node[r].leader = r
  /\ node[r].balPrepared > 0
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ pending /= <<>>
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Empty"
       /\ \A t \in Slots : t < s => node[r].insts[t].status /= "Empty"
       /\ LET c == Head(pending)
              b == node[r].balPrepared
          IN /\ node' = [node EXCEPT ![r].insts[s] =
                           [status |-> "Accepting", cmd |-> c,
                            voted |-> [bal |-> b, cmd |-> c], voters |-> {r}]]
             /\ msgs' = msgs \cup
                  {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s,
                    cmd |-> c]}
             /\ pending' = Tail(pending)
             /\ observed' = Append(observed, ReqEvent(c))

HandleAccept(r) ==
  \E m \in msgs :
    /\ m.type = "Accept"
    /\ m.src /= r
    /\ m.bal >= node[r].balMaxKnown
    /\ [type |-> "AcceptReply", src |-> r, dst |-> m.src, bal |-> m.bal,
        slot |-> m.slot] \notin msgs
    /\ node' = [node EXCEPT
                  ![r].leader = m.src,
                  ![r].balMaxKnown = m.bal,
                  ![r].prepVoters = IF m.bal > node[r].balMaxKnown THEN {}
                                                                   ELSE @,
                  ![r].insts[m.slot] =
                      IF node[r].insts[m.slot].status = "Committed"
                        THEN node[r].insts[m.slot]
                        ELSE [status |-> "Accepting", cmd |-> m.cmd,
                              voted |-> [bal |-> m.bal, cmd |-> m.cmd],
                              voters |-> {}]]
    /\ msgs' = msgs \cup
         {[type |-> "AcceptReply", src |-> r, dst |-> m.src, bal |-> m.bal,
           slot |-> m.slot]}
    /\ UNCHANGED <<pending, observed>>

HandleAcceptReply(r) ==
  \E m \in msgs :
    /\ m.type = "AcceptReply"
    /\ m.dst = r
    /\ node[r].leader = r
    /\ m.bal = node[r].balPrepared
    /\ m.bal = node[r].balMaxKnown
    /\ node[r].insts[m.slot].status = "Accepting"
    /\ node[r].insts[m.slot].voted.bal = m.bal
    /\ m.src \notin node[r].insts[m.slot].voters
    /\ node' = [node EXCEPT ![r].insts[m.slot].voters = @ \cup {m.src}]
    /\ UNCHANGED <<msgs, pending, observed>>

FinishAccept(r) ==
  \E s \in Slots :
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ node[r].insts[s].status = "Accepting"
    /\ node[r].insts[s].voted.bal = node[r].balPrepared
    /\ Cardinality(node[r].insts[s].voters) >= MajorityNum
    /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
    /\ UNCHANGED <<msgs, pending, observed>>

ResultAt(r, s) ==
  LET c  == node[r].insts[s].cmd
      ws == {t \in Slots : t < s /\ node[r].insts[t].cmd.type = "Put"}
  IN IF c.type = "Put" THEN c.val
     ELSE IF ws = {} THEN NoValue
          ELSE node[r].insts[Max(ws)].cmd.val

ReplyClient(r) ==
  /\ node[r].leader = r
  /\ \E s \in Slots :
       /\ node[r].insts[s].status = "Committed"
       /\ \A t \in Slots : t < s => node[r].insts[t].status = "Committed"
       /\ LET c == node[r].insts[s].cmd
          IN /\ c \in Commands
             /\ \E i \in ReqPositions : observed[i].cmd = c
             /\ ~ Acked(c)
             /\ observed' = Append(observed, AckEvent(c, ResultAt(r, s)))
  /\ UNCHANGED <<msgs, node, pending>>

Next ==
  \/ \E r \in Replicas :
       \/ BecomeLeader(r)
       \/ HandlePrepare(r)
       \/ HandlePrepareReply(r)
       \/ FinishPrepare(r)
       \/ TakeNewRequest(r)
       \/ HandleAccept(r)
       \/ HandleAcceptReply(r)
       \/ FinishAccept(r)
       \/ ReplyClient(r)
  \/ (Terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
  /\ msgs \subseteq Messages
  /\ node \in [Replicas -> NodeStates]
  /\ pending \in Seq(Commands)
  /\ observed \in Seq(ClientEvents)
  /\ Len(pending) + Cardinality(ReqPositions) = NumCommands
  /\ Cardinality(ReqPositions) <= NumCommands
  /\ Cardinality(AckPositions) <= Cardinality(ReqPositions)

-----------------------------------------------------------------------------
(* Linearizability over observed client events *)

ReqPosOfCmd(c) ==
  CHOOSE i \in 1..Len(observed) :
    observed[i].type = "Req" /\ observed[i].cmd = c

AckPosOfCmd(c) ==
  CHOOSE i \in 1..Len(observed) :
    observed[i].type = "Ack" /\ observed[i].cmd = c

ResultOfCmd(c) == observed[AckPosOfCmd(c)].val

OrderIdxOfCmd(order, c) == CHOOSE j \in 1..Len(order) : order[j] = c

WriteOfValue(v) == [type |-> "Put", val |-> v]

\* Write order constraints: each Get observes the most recent preceding Put.
WriteOrderOK(order) ==
  \A c \in Commands :
    c.type = "Get" =>
      LET j == OrderIdxOfCmd(order, c)
          v == ResultOfCmd(c)
      IN IF v = NoValue
           THEN \A k \in 1..(j - 1) : order[k].type /= "Put"
           ELSE LET w == OrderIdxOfCmd(order, WriteOfValue(v))
                IN /\ w < j
                   /\ \A k \in (w + 1)..(j - 1) : order[k].type /= "Put"

\* Real-time ordering: if c1 was acked before c2 was requested, c1 precedes c2.
RealTimeOK(order) ==
  \A c1, c2 \in Commands :
    AckPosOfCmd(c1) < ReqPosOfCmd(c2) =>
      OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2)

Linearizability ==
  Terminated =>
    \E order \in Orders :
      /\ WriteOrderOK(order)
      /\ RealTimeOK(order)

-----------------------------------------------------------------------------
(* Top-level correctness theorems *)

THEOREM TypeCorrectness == Spec => []TypeOK

THEOREM Linearizable == Spec => []Linearizability

=============================================================================