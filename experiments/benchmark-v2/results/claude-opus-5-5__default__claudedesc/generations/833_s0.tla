------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME /\ Cardinality(Replicas) >= 1
       /\ Cardinality(Writes) >= 1
       /\ MaxBallot \in Nat
       /\ MaxBallot >= 2

VARIABLES msgs, node, pending, observed

vars == <<msgs, node, pending, observed>>

----------------------------------------------------------------------------
(* Helper definitions *)

Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
NumReplicas == Cardinality(Replicas)
Majority    == (NumReplicas \div 2) + 1

Slots    == 1..NumCommands
Ballots  == 1..MaxBallot
Statuses == {"Empty", "Preparing", "Accepting", "Committed"}

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

RIdx == CHOOSE f \in [Replicas -> 0..(NumReplicas - 1)] :
            \A a, b \in Replicas : a # b => f[a] # f[b]

Owns(r, b) == b % NumReplicas = RIdx[r]

AllPerms == {s \in [1..NumCommands -> Commands] :
                \A i, j \in 1..NumCommands : i # j => s[i] # s[j]}

NullVote == [bal |-> 0, cmd |-> "nil"]
NullInst == [status |-> "Empty", cmd |-> "nil", voted |-> NullVote]

VoteStates == [bal : Ballots \cup {0}, cmd : Commands \cup {"nil", "nop"}]
InstStates == [status : Statuses,
               cmd    : Commands \cup {"nil", "nop"},
               voted  : VoteStates]

NodeStates == [leader      : Replicas \cup {"none"},
               kvalue      : Writes \cup {"nil"},
               commitUpTo  : Slots \cup {0},
               balPrepared : Ballots \cup {0},
               balMaxKnown : Ballots \cup {0},
               insts       : [Slots -> InstStates]]

Acked(c) == \E i \in 1..Len(observed) :
               observed[i].type = "ack" /\ observed[i].cmd = c

----------------------------------------------------------------------------
TypeOK ==
    /\ node \in [Replicas -> NodeStates]
    /\ \A i \in 1..Len(pending) : pending[i] \in Commands
    /\ \A i \in 1..Len(observed) : observed[i].type \in {"req", "ack"}

Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |->
                 [leader      |-> "none",
                  kvalue      |-> "nil",
                  commitUpTo  |-> 0,
                  balPrepared |-> 0,
                  balMaxKnown |-> 0,
                  insts       |-> [s \in Slots |-> NullInst]]]
    /\ pending \in AllPerms
    /\ observed = <<>>

----------------------------------------------------------------------------
(* Replica r becomes leader by broadcasting Prepare with a fresh ballot. *)
BecomeLeader(r) ==
    \E b \in Ballots :
        /\ b > node[r].balMaxKnown
        /\ Owns(r, b)
        /\ node' = [node EXCEPT
                      ![r].leader = r,
                      ![r].balMaxKnown = b,
                      ![r].insts = [s \in Slots |->
                          IF node[r].insts[s].status = "Accepting"
                          THEN [node[r].insts[s] EXCEPT !.status = "Preparing"]
                          ELSE node[r].insts[s]]]
        /\ msgs' = msgs \cup
                   {[type |-> "Prepare", src |-> r, bal |-> b],
                    [type |-> "PrepareReply", src |-> r, bal |-> b,
                     voteds |-> [s \in Slots |-> node[r].insts[s].voted]]}
        /\ UNCHANGED <<pending, observed>>

(* Replica r responds to a Prepare with its voted commands. *)
HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > node[r].balMaxKnown
        /\ node' = [node EXCEPT
                      ![r].leader = m.src,
                      ![r].balMaxKnown = m.bal]
        /\ msgs' = msgs \cup
                   {[type |-> "PrepareReply", src |-> r, bal |-> m.bal,
                     voteds |-> [s \in Slots |-> node[r].insts[s].voted]]}
        /\ UNCHANGED <<pending, observed>>

(* Leader r gathers PrepareReplies from a majority and completes preparation. *)
HandlePrepareReplies(r) ==
    LET b == node[r].balMaxKnown IN
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared < b
    /\ \E Q \in SUBSET Replicas :
         /\ Cardinality(Q) >= Majority
         /\ \A q \in Q : \E m \in msgs :
               m.type = "PrepareReply" /\ m.src = q /\ m.bal = b
         /\ LET prs == {m \in msgs : /\ m.type = "PrepareReply"
                                     /\ m.bal = b
                                     /\ m.src \in Q}
                votesAt(s) == {v \in {m.voteds[s] : m \in prs} : v.bal > 0}
                hasVote(s) == votesAt(s) # {}
                best(s) == CHOOSE v \in votesAt(s) :
                               \A w \in votesAt(s) : w.bal <= v.bal
                votedSlots == {s \in Slots : hasVote(s)}
                maxVoted == IF votedSlots = {} THEN 0 ELSE MaxOf(votedSlots)
                reprop(s) == /\ node[r].insts[s].status # "Committed"
                             /\ (hasVote(s) \/ s < maxVoted)
                newCmd(s) == IF hasVote(s) THEN best(s).cmd ELSE "nop"
                repSlots == {s \in Slots : reprop(s)}
            IN
            /\ node' = [node EXCEPT
                  ![r].balPrepared = b,
                  ![r].insts = [s \in Slots |->
                      IF reprop(s)
                      THEN [status |-> "Accepting",
                            cmd    |-> newCmd(s),
                            voted  |-> [bal |-> b, cmd |-> newCmd(s)]]
                      ELSE IF node[r].insts[s].status = "Committed"
                           THEN node[r].insts[s]
                           ELSE [status |-> "Empty",
                                 cmd    |-> "nil",
                                 voted  |-> node[r].insts[s].voted]]]
            /\ msgs' = msgs
                 \cup {[type |-> "Accept", src |-> r, bal |-> b,
                        slot |-> s, cmd |-> newCmd(s)] : s \in repSlots}
                 \cup {[type |-> "AcceptReply", src |-> r, bal |-> b,
                        slot |-> s] : s \in repSlots}
    /\ UNCHANGED <<pending, observed>>

(* Prepared leader r accepts a new client request into an empty slot. *)
TakeNewRequest(r) ==
    LET b == node[r].balMaxKnown IN
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared = b
    /\ pending # <<>>
    /\ \E s \in Slots :
         /\ node[r].insts[s].status = "Empty"
         /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
         /\ LET c == Head(pending) IN
            /\ node' = [node EXCEPT
                  ![r].insts[s] = [status |-> "Accepting",
                                   cmd    |-> c,
                                   voted  |-> [bal |-> b, cmd |-> c]]]
            /\ msgs' = msgs \cup
                 {[type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c],
                  [type |-> "AcceptReply", src |-> r, bal |-> b, slot |-> s]}
            /\ pending' = Tail(pending)
            /\ observed' = Append(observed,
                              [type |-> "req", cmd |-> c, val |-> "nil"])

(* Replica r votes on an Accept message. *)
HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= node[r].balMaxKnown
        /\ node[r].insts[m.slot].status # "Committed"
        /\ m.bal > node[r].insts[m.slot].voted.bal
        /\ node' = [node EXCEPT
              ![r].leader = m.src,
              ![r].balMaxKnown = m.bal,
              ![r].insts[m.slot] = [status |-> "Accepting",
                                    cmd    |-> m.cmd,
                                    voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
        /\ msgs' = msgs \cup
             {[type |-> "AcceptReply", src |-> r, bal |-> m.bal, slot |-> m.slot]}
        /\ UNCHANGED <<pending, observed>>

(* Leader r commits the next slot upon a majority of AcceptReplies. *)
HandleAcceptReplies(r) ==
    LET b == node[r].balMaxKnown
        s == node[r].commitUpTo + 1
    IN
    /\ node[r].leader = r
    /\ b > 0
    /\ node[r].balPrepared = b
    /\ s \in Slots
    /\ node[r].insts[s].status = "Accepting"
    /\ node[r].insts[s].voted.bal = b
    /\ Cardinality({m.src : m \in {m \in msgs : /\ m.type = "AcceptReply"
                                                /\ m.bal = b
                                                /\ m.slot = s}}) >= Majority
    /\ LET c == node[r].insts[s].cmd
           newVal == IF c \in Writes THEN c ELSE node[r].kvalue
       IN
       /\ node' = [node EXCEPT
             ![r].insts[s].status = "Committed",
             ![r].commitUpTo = s,
             ![r].kvalue = newVal]
       /\ msgs' = msgs \cup {[type |-> "CommitNotice", slot |-> s, cmd |-> c]}
       /\ observed' = IF c \in Commands /\ ~Acked(c)
                      THEN Append(observed,
                             [type |-> "ack", cmd |-> c,
                              val  |-> IF c \in Reads THEN node[r].kvalue
                                                      ELSE "nil"])
                      ELSE observed
    /\ UNCHANGED pending

(* Follower r learns a committed slot via CommitNotice. *)
HandleCommitNotice(r) ==
    \E m \in msgs :
        /\ m.type = "CommitNotice"
        /\ m.slot = node[r].commitUpTo + 1
        /\ node' = [node EXCEPT
              ![r].insts[m.slot] = [status |-> "Committed",
                                    cmd    |-> m.cmd,
                                    voted  |-> node[r].insts[m.slot].voted],
              ![r].commitUpTo = m.slot,
              ![r].kvalue = IF m.cmd \in Writes THEN m.cmd
                                                ELSE node[r].kvalue]
        /\ UNCHANGED <<msgs, pending, observed>>

----------------------------------------------------------------------------
Terminated ==
    /\ pending = <<>>
    /\ \A c \in Commands : Acked(c)

Progress ==
    \E r \in Replicas :
        \/ BecomeLeader(r)
        \/ HandlePrepare(r)
        \/ HandlePrepareReplies(r)
        \/ TakeNewRequest(r)
        \/ HandleAccept(r)
        \/ HandleAcceptReplies(r)
        \/ HandleCommitNotice(r)

Next ==
    \/ Progress
    \/ (Terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Deadlock freedom: progress is possible until all requests are observed. *)
NoDeadlock == Terminated \/ ENABLED Progress

(* Linearizability of client-observed request/ack history after termination. *)
ReqPos(c) == CHOOSE i \in 1..Len(observed) :
                observed[i].type = "req" /\ observed[i].cmd = c
AckPos(c) == CHOOSE i \in 1..Len(observed) :
                observed[i].type = "ack" /\ observed[i].cmd = c
AckVal(c) == observed[AckPos(c)].val

LastWriteBefore(ord, i) ==
    LET ws == {j \in 1..(i - 1) : ord[j] \in Writes}
    IN IF ws = {} THEN "nil" ELSE ord[MaxOf(ws)]

IsLinearizable ==
    \E ord \in AllPerms :
        /\ \A i, j \in 1..NumCommands :
              AckPos(ord[j]) < ReqPos(ord[i]) => j < i
        /\ \A i \in 1..NumCommands :
              ord[i] \in Reads => AckVal(ord[i]) = LastWriteBefore(ord, i)

Linearizability == Terminated => IsLinearizable

=============================================================================