```tla
]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

ClientEvents ==
    {ReqEvent(c) : c \in Commands}
    \cup {AckEvent(c, v) : c \in Commands, v \in Writes \cup {NullVal}}

(* Server-side state *)
CmdVals    == Commands \cup {NullCmd, NoOp}
Votes      == [bal : Ballots, cmd : CmdVals]
NullVote   == [bal |-> 0, cmd |-> NullCmd]
InstStatus == {"Empty", "Accepting", "Committed"}
Insts      == [status : InstStatus, cmd : CmdVals, voted : Votes]
EmptyInst  == [status |-> "Empty", cmd |-> NullCmd, voted |-> NullVote]
NodeStatus == {"Following", "Preparing", "Leading"}

NodeStates == [leader      : Replicas \cup {NoLeader},
               status      : NodeStatus,
               balPrepared : Ballots,
               balMaxKnown : Ballots,
               insts       : [Slots -> Insts]]

InitNode == [leader      |-> NoLeader,
             status      |-> "Following",
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts       |-> [s \in Slots |-> EmptyInst]]

(* Message types *)
PrepareMsg(r, b) ==
    [type |-> "Prepare", src |-> r, bal |-> b]

PrepareReplyMsg(r, d, b, vs) ==
    [type |-> "PrepareReply", src |-> r, dst |-> d, bal |-> b, votes |-> vs]

AcceptMsg(r, b, s, c) ==
    [type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c]

AcceptReplyMsg(r, d, b, s) ==
    [type |-> "AcceptReply", src |-> r, dst |-> d, bal |-> b, slot |-> s]

-----------------------------------------------------------------------------
VARIABLES msgs,      \* monotonic set of all sent messages
          node,      \* per-replica server state
          pending,   \* commands not yet requested by clients
          observed   \* client-observed sequence of Req/Ack events

vars == <<msgs, node, pending, observed>>

(* Client-observation helpers *)
Requested(c) == \E i \in DOMAIN observed :
                    observed[i].type = "Req" /\ observed[i].cmd = c
Acked(c)     == \E i \in DOMAIN observed :
                    observed[i].type = "Ack" /\ observed[i].cmd = c

ReqPos(c) == CHOOSE i \in DOMAIN observed :
                 observed[i].type = "Req" /\ observed[i].cmd = c
AckPos(c) == CHOOSE i \in DOMAIN observed :
                 observed[i].type = "Ack" /\ observed[i].cmd = c

AckedCmds     == {c \in Commands : Acked(c)}
RequestedCmds == Commands \ pending

Terminated == \A c \in Commands : Acked(c)

VotesOf(r) == [s \in Slots |-> node[r].insts[s].voted]

-----------------------------------------------------------------------------
Init ==
    /\ msgs     = {}
    /\ node     = [r \in Replicas |-> InitNode]
    /\ pending  = Commands
    /\ observed = <<>>

(* A client issues a new request. *)
ClientRequest(c) ==
    /\ c \in pending
    /\ pending'  = pending \ {c}
    /\ observed' = Append(observed, ReqEvent(c))
    /\ UNCHANGED <<msgs, node>>

(* Replica r tries to become leader with one of its own ballots, b. *)
BecomeLeader(r, b) ==
    /\ b \in BallotsOf(r)
    /\ b > node[r].balMaxKnown
    /\ node' = [node EXCEPT ![r].status      = "Preparing",
                            ![r].balMaxKnown = b,
                            ![r].leader      = r]
    /\ msgs' = msgs \cup {PrepareMsg(r, b)}
    /\ UNCHANGED <<pending, observed>>

(* Replica r answers a Prepare, at most once per ballot. *)
HandlePrepare(r) ==
    \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal >= node[r].balMaxKnown
        /\ ~\E m2 \in msgs : /\ m2.type = "PrepareReply"
                             /\ m2.src  = r
                             /\ m2.bal  = m.bal
        /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal,
                                ![r].leader      = m.src,
                                ![r].status      = IF m.src = r THEN @
                                                   ELSE "Following"]
        /\ msgs' = msgs \cup {PrepareReplyMsg(r, m.src, m.bal, VotesOf(r))}
        /\ UNCHANGED <<pending, observed>>
```

```tla
(* Leader r gathers a majority of PrepareReplies. It recovers the log,  *)
(* fills holes with no-ops, re-proposes recovered slots, and starts     *)
(* leading.                                                              *)
PrepareQuorum(r) ==
    LET b == node[r].balMaxKnown IN
    /\ node[r].status = "Preparing"
    /\ \E Q \in Quorums :
        LET replies == {m \in msgs : /\ m.type = "PrepareReply"
                                     /\ m.dst  = r
                                     /\ m.bal  = b
                                     /\ m.src  \in Q}
            VotesAt(s) == {m.votes[s] : m \in replies}
            MaxVote(s) == CHOOSE v \in VotesAt(s) :
                              \A w \in VotesAt(s) : w.bal <= v.bal
            RecSlots   == {s \in Slots : MaxVote(s).bal > 0}
            TopSlot    == IF RecSlots = {} THEN 0 ELSE Max(RecSlots)
            old        == node[r].insts
            NewInst(s) ==
                IF old[s].status = "Committed" THEN old[s]
                ELSE IF s \in RecSlots
                     THEN [status |-> "Accepting", cmd |-> MaxVote(s).cmd,
                           voted  |-> old[s].voted]
                ELSE IF s < TopSlot
                     THEN [status |-> "Accepting", cmd |-> NoOp,
                           voted  |-> old[s].voted]
                ELSE [status |-> "Empty", cmd |-> NullCmd,
                      voted  |-> old[s].voted]
            newInsts == [s \in Slots |-> NewInst(s)]
            accSlots == {s \in Slots : newInsts[s].status = "Accepting"}
        IN /\ \A q \in Q : \E m \in replies : m.src = q
           /\ node' = [node EXCEPT ![r].status      = "Leading",
                                   ![r].balPrepared = b,
                                   ![r].insts       = newInsts]
           /\ msgs' = msgs \cup
                        {AcceptMsg(r, b, s, newInsts[s].cmd) : s \in accSlots}
    /\ UNCHANGED <<pending, observed>>

(* The current leader proposes a requested command it has not yet     *)
(* logged, placing it in the first empty slot.                          *)
TakeNewRequest(r, c) ==
    LET b   == node[r].balPrepared
        ins == node[r].insts
    IN
    /\ node[r].status = "Leading"
    /\ b = node[r].balMaxKnown
    /\ c \in RequestedCmds
    /\ ~Acked(c)
    /\ \A s \in Slots : ins[s].cmd # c
    /\ \E s \in Slots :
        /\ ins[s].status = "Empty"
        /\ \A t \in 1..(s - 1) : ins[t].status # "Empty"
        /\ node' = [node EXCEPT ![r].insts[s].status = "Accepting",
                                ![r].insts[s].cmd    = c]
        /\ msgs' = msgs \cup {AcceptMsg(r, b, s, c)}
    /\ UNCHANGED <<pending, observed>>

(* Replica r votes for an Accept, replying once per (ballot, slot). *)
HandleAccept(r) ==
    \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= node[r].balMaxKnown
        /\ AcceptReplyMsg(r, m.src, m.bal, m.slot) \notin msgs
        /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal,
                                ![r].leader      = m.src,
                                ![r].status      = IF m.src = r THEN @
                                                   ELSE "Following",
                                ![r].insts[m.slot].voted =
                                    [bal |-> m.bal, cmd |-> m.cmd]]
        /\ msgs' = msgs \cup {AcceptReplyMsg(r, m.src, m.bal, m.slot)}
        /\ UNCHANGED <<pending, observed>>

(* Leader r commits slot s once a majority has accepted it. *)
Commit(r, s) ==
    /\ node[r].status = "Leading"
    /\ node[r].insts[s].status = "Accepting"
    /\ \E Q \in Quorums :
        \A q \in Q : AcceptReplyMsg(q, r, node[r].balPrepared, s) \in msgs
    /\ node' = [node EXCEPT ![r].insts[s].status = "Committed"]
    /\ UNCHANGED <<msgs, pending, observed>>

(* Leader r executes the committed prefix up to slot s and acknowledges *)
(* the command there. Only the first occurrence of a command takes      *)
(* effect.                                                               *)
ClientAck(r, s) ==
    LET ins == node[r].insts
        c   == ins[s].cmd
        EffWrites == {t \in 1..(s - 1) :
                        /\ ins[t].cmd \in Writes
                        /\ \A u \in 1..(t - 1) : ins[u].cmd # ins[t].cmd}
        val == IF c \in Writes THEN c
               ELSE IF EffWrites = {} THEN NullVal
               ELSE ins[Max(EffWrites)].cmd
    IN
    /\ node[r].status = "Leading"
    /\ \A t \in 1..s : ins[t].status = "Committed"
    /\ c \in Commands
    /\ \A t \in 1..(s - 1) : ins[t].cmd # c
    /\ ~Acked(c)
    /\ observed' = Append(observed, AckEvent(c, val))
    /\ UNCHANGED <<msgs, node, pending>>

(* Once every request is acknowledged, stutter instead of deadlocking. *)
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Commands : ClientRequest(c)
    \/ \E r \in Replicas :
        \/ \E b \in Ballots : BecomeLeader(r, b)
        \/ HandlePrepare(r)
        \/ PrepareQuorum(r)
        \/ \E c \in Commands : TakeNewRequest(r, c)
        \/ HandleAccept(r)
        \/ \E s \in Slots : Commit(r, s)
        \/ \E s \in Slots : ClientAck(r, s)
    \/ Done

Fairness ==
    /\ \A c \in Commands : WF_vars(ClientRequest(c))
    /\ \A r \in Replicas :
        /\ \A b \in Ballots : WF_vars(BecomeLeader(r, b))
        /\ WF_vars(HandlePrepare(r))
        /\ WF_vars(PrepareQuorum(r))
        /\ \A c \in Commands : WF_vars(TakeNewRequest(r, c))
        /\ WF_vars(HandleAccept(r))
        /\ \A s \in Slots : WF_vars(Commit(r, s))
        /\ \A s \in Slots : WF_vars(ClientAck(r, s))

Spec == Init /\ [][Next]_vars /\ Fairness
```

```tla
-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ node \in [Replicas -> NodeStates]
    /\ pending \subseteq Commands
    /\ observed \in Seq(ClientEvents)

\* Every acknowledgement is preceded by its request, and each command
\* is requested and acknowledged at most once.
ObservedWellFormed ==
    /\ \A c \in AckedCmds : Requested(c) /\ ReqPos(c) < AckPos(c)
    /\ \A i, j \in DOMAIN observed :
         (i # j /\ observed[i].type = observed[j].type)
            => observed[i].cmd # observed[j].cmd

\* All replicas agree on every committed slot.
CommittedConsistency ==
    \A r1, r2 \in Replicas, s \in Slots :
        (/\ node[r1].insts[s].status = "Committed"
         /\ node[r2].insts[s].status = "Committed")
            => node[r1].insts[s].cmd = node[r2].insts[s].cmd

\* Value a command returns at position i of a sequential order.
ExpectedVal(ord, i) ==
    IF ord[i] \in Writes THEN ord[i]
    ELSE LET W == {j \in 1..(i - 1) : ord[j] \in Writes}
         IN IF W = {} THEN NullVal ELSE ord[Max(W)]

\* Linearizability from the client's view: some sequential order of a set
\* of requested commands (containing every acknowledged one) respects
\* real-time order, and every acknowledged value matches that order.
Linearizability ==
    \E S \in SUBSET RequestedCmds :
        /\ AckedCmds \subseteq S
        /\ \E ord \in [1..Cardinality(S) -> S] :
            /\ \A i, j \in DOMAIN ord : i # j => ord[i] # ord[j]
            /\ \A i, j \in DOMAIN ord :
                 (/\ ord[i] \in AckedCmds
                  /\ AckPos(ord[i]) < ReqPos(ord[j]))
                    => i < j
            /\ \A i \in DOMAIN ord :
                 ord[i] \in AckedCmds =>
                    observed[AckPos(ord[i])].val = ExpectedVal(ord, i)

(* Liveness: every request is eventually acknowledged. *)
AllRequestsAcked == <>Terminated

THEOREM Spec => [](TypeOK /\ CommittedConsistency /\ Linearizability)
=============================================================================
```