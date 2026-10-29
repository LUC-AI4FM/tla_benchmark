---------------------------- MODULE MultiPaxos ----------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME /\ Replicas # {}
       /\ IsFiniteSet(Replicas)
       /\ IsFiniteSet(Writes) /\ IsFiniteSet(Reads)
       /\ Writes \cap Reads = {}
       /\ "nil" \notin (Writes \cup Reads)
       /\ "none" \notin Replicas
       /\ MaxBallot \in Nat

Commands    == Writes \cup Reads
NumCommands == Cardinality(Commands)
Slots       == 1..NumCommands
Ballots     == 0..MaxBallot
N           == Cardinality(Replicas)
Quorums     == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > N}

ReplicaSeq  == CHOOSE f \in [1..N -> Replicas] :
                  \A r \in Replicas : \E i \in 1..N : f[i] = r
Owner(b)    == ReplicaSeq[(b % N) + 1]

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

NoVote    == [bal |-> -1, cmd |-> "nil"]
NoVotes   == [s \in Slots |-> NoVote]
EmptyInst == [status |-> "Empty", cmd |-> "nil", voted |-> NoVote]

Msg(t, src, b, s, c, v) ==
    [type |-> t, src |-> src, bal |-> b, slot |-> s, cmd |-> c, voted |-> v]

ReqEvent(c)    == [type |-> "Req", cmd |-> c, val |-> "nil"]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

\* value returned by a read in slot s: latest write before s in the log
ReadVal(insts, s) ==
    LET ws == {t \in 1..(s-1) : insts[t].cmd \in Writes}
    IN  IF ws = {} THEN "nil" ELSE insts[Max(ws)].cmd

VARIABLES msgs,       \* monotonic set of sent messages
          node,       \* per-replica state
          pc,         \* per-replica control state
          requested,  \* commands issued by clients so far
          pending,    \* issued but not yet acknowledged commands
          observed    \* client-observed sequence of Req/Ack events

vars == <<msgs, node, pc, requested, pending, observed>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Replicas -> {"rloop", "Done"}]
    /\ requested \subseteq Commands
    /\ pending \subseteq Commands
    /\ \A r \in Replicas :
         /\ node[r].leader \in Replicas \cup {"none"}
         /\ node[r].balPrepared \in Ballots \cup {-1}
         /\ node[r].balMaxKnown \in Ballots \cup {-1}
         /\ \A s \in Slots :
              /\ node[r].insts[s].status \in {"Empty", "Accepting", "Committed"}
              /\ node[r].insts[s].cmd \in Commands \cup {"nil"}

Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |->
                 [leader      |-> "none",
                  balPrepared |-> -1,
                  balMaxKnown |-> -1,
                  insts       |-> [s \in Slots |-> EmptyInst]]]
    /\ pc = [r \in Replicas |-> "rloop"]
    /\ requested = {}
    /\ pending = {}
    /\ observed = <<>>

-----------------------------------------------------------------------------
\* Client issues a request
ClientRequest(c) ==
    /\ c \in Commands \ requested
    /\ requested' = requested \cup {c}
    /\ pending' = pending \cup {c}
    /\ observed' = Append(observed, ReqEvent(c))
    /\ UNCHANGED <<msgs, node, pc>>

\* Phase 1a: replica r starts preparing a new ballot it owns
Prepare(r) ==
    /\ pc[r] = "rloop"
    /\ \E b \in Ballots :
         /\ Owner(b) = r
         /\ b > node[r].balMaxKnown
         /\ node' = [node EXCEPT ![r].balMaxKnown = b, ![r].leader = "none"]
         /\ msgs' = msgs \cup {Msg("Prepare", r, b, 0, "nil", NoVotes)}
    /\ UNCHANGED <<pc, requested, pending, observed>>

\* Phase 1b: replica r replies to a Prepare
HandlePrepare(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Prepare"
         /\ m.bal >= node[r].balMaxKnown
         /\ LET reply == Msg("PrepareReply", r, m.bal, 0, "nil",
                             [s \in Slots |-> node[r].insts[s].voted])
            IN  /\ reply \notin msgs
                /\ msgs' = msgs \cup {reply}
         /\ node' = [node EXCEPT ![r].balMaxKnown = m.bal,
                                 ![r].leader = IF m.bal > node[r].balMaxKnown
                                               THEN m.src ELSE @]
    /\ UNCHANGED <<pc, requested, pending, observed>>

\* Leader r gathers a quorum of PrepareReplies and becomes leader
BecomeLeader(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ b >= 0
    /\ Owner(b) = r
    /\ node[r].balPrepared < b
    /\ \E Q \in Quorums :
         LET replies == {m \in msgs : m.type = "PrepareReply"
                                       /\ m.bal = b /\ m.src \in Q}
             votes(s) == {m.voted[s] : m \in replies}
             best(s)  == CHOOSE v \in votes(s) :
                           \A w \in votes(s) : w.bal <= v.bal
             old      == node[r].insts
             newInsts == [s \in Slots |->
                           IF old[s].status = "Committed" THEN old[s]
                           ELSE IF best(s).bal >= 0
                                THEN [status |-> "Accepting",
                                      cmd    |-> best(s).cmd,
                                      voted  |-> [bal |-> b, cmd |-> best(s).cmd]]
                                ELSE [status |-> "Empty", cmd |-> "nil",
                                      voted  |-> old[s].voted]]
             acc == {s \in Slots : newInsts[s].status = "Accepting"}
         IN  /\ \A q \in Q : \E m \in replies : m.src = q
             /\ node' = [node EXCEPT ![r].balPrepared = b,
                                     ![r].leader = r,
                                     ![r].insts = newInsts]
             /\ msgs' = msgs
                        \cup {Msg("Accept", r, b, s, newInsts[s].cmd, NoVotes) : s \in acc}
                        \cup {Msg("AcceptReply", r, b, s, newInsts[s].cmd, NoVotes) : s \in acc}
    /\ UNCHANGED <<pc, requested, pending, observed>>

\* Phase 2a: leader proposes a pending command in the first empty slot
Propose(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ node[r].leader = r
    /\ node[r].balPrepared = b
    /\ b >= 0
    /\ \E c \in pending :
         /\ \A s \in Slots : node[r].insts[s].cmd # c
         /\ \E s \in Slots :
              /\ node[r].insts[s].status = "Empty"
              /\ \A t \in Slots : t < s => node[r].insts[t].status # "Empty"
              /\ node' = [node EXCEPT ![r].insts[s] =
                            [status |-> "Accepting", cmd |-> c,
                             voted  |-> [bal |-> b, cmd |-> c]]]
              /\ msgs' = msgs \cup {Msg("Accept", r, b, s, c, NoVotes),
                                    Msg("AcceptReply", r, b, s, c, NoVotes)}
    /\ UNCHANGED <<pc, requested, pending, observed>>

\* Phase 2b: replica r accepts a proposal
HandleAccept(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "Accept"
         /\ m.bal >= node[r].balMaxKnown
         /\ LET reply == Msg("AcceptReply", r, m.bal, m.slot, m.cmd, NoVotes)
            IN  /\ reply \notin msgs
                /\ msgs' = msgs \cup {reply}
         /\ node' = [node EXCEPT
                       ![r].balMaxKnown = m.bal,
                       ![r].leader = m.src,
                       ![r].insts[m.slot] =
                          IF @.status = "Committed" THEN @
                          ELSE [status |-> "Accepting", cmd |-> m.cmd,
                                voted  |-> [bal |-> m.bal, cmd |-> m.cmd]]]
    /\ UNCHANGED <<pc, requested, pending, observed>>

\* Leader commits a slot (in order), sends commit notice, acks client
Commit(r) ==
    LET b == node[r].balMaxKnown IN
    /\ pc[r] = "rloop"
    /\ node[r].leader = r
    /\ node[r].balPrepared = b
    /\ b >= 0
    /\ \E s \in Slots :
         LET c        == node[r].insts[s].cmd
             newInsts == [node[r].insts EXCEPT ![s].status = "Committed"]
         IN
         /\ node[r].insts[s].status = "Accepting"
         /\ \A t \in Slots : t < s => node[r].insts[t].status = "Committed"
         /\ \E Q \in Quorums :
              \A q \in Q : Msg("AcceptReply", q, b, s, c, NoVotes) \in msgs
         /\ node' = [node EXCEPT ![r].insts = newInsts]
         /\ msgs' = msgs \cup {Msg("CommitNotice", r, b, s, c, NoVotes)}
         /\ IF c \in pending
              THEN /\ pending' = pending \ {c}
                   /\ observed' = Append(observed,
                        AckEvent(c, IF c \in Writes THEN c
                                    ELSE ReadVal(newInsts, s)))
              ELSE UNCHANGED <<pending, observed>>
    /\ UNCHANGED <<pc, requested>>

\* Replica learns a committed slot from a commit notice
HandleCommitNotice(r) ==
    /\ pc[r] = "rloop"
    /\ \E m \in msgs :
         /\ m.type = "CommitNotice"
         /\ node[r].insts[m.slot].status # "Committed"
         /\ node' = [node EXCEPT ![r].insts[m.slot].status = "Committed",
                                 ![r].insts[m.slot].cmd = m.cmd]
    /\ UNCHANGED <<msgs, pc, requested, pending, observed>>

\* Replica finishes once all slots are committed
ReplicaDone(r) ==
    /\ pc[r] = "rloop"
    /\ \A s \in Slots : node[r].insts[s].status = "Committed"
    /\ pc' = [pc EXCEPT ![r] = "Done"]
    /\ UNCHANGED <<msgs, node, requested, pending, observed>>

ReplicaStep(r) ==
    \/ Prepare(r)
    \/ HandlePrepare(r)
    \/ BecomeLeader(r)
    \/ Propose(r)
    \/ HandleAccept(r)
    \/ Commit(r)
    \/ HandleCommitNotice(r)
    \/ ReplicaDone(r)

\* Explicit stuttering to avoid deadlock after termination
Terminating ==
    /\ \A r \in Replicas : pc[r] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Commands : ClientRequest(c)
    \/ \E r \in Replicas : ReplicaStep(r)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A r \in Replicas : WF_vars(ReplicaStep(r))
    /\ \A c \in Commands : WF_vars(ClientRequest(c))

-----------------------------------------------------------------------------
\* Safety properties

Agreement ==
    \A r1, r2 \in Replicas, s \in Slots :
       (node[r1].insts[s].status = "Committed" /\
        node[r2].insts[s].status = "Committed")
         => node[r1].insts[s].cmd = node[r2].insts[s].cmd

AckAfterReq ==
    \A i \in 1..Len(observed) :
       observed[i].type = "Ack" =>
          \E j \in 1..(i-1) : observed[j] = ReqEvent(observed[i].cmd)

AckAtMostOnce ==
    \A i, j \in 1..Len(observed) :
       (observed[i].type = "Ack" /\ observed[j].type = "Ack" /\
        observed[i].cmd = observed[j].cmd) => i = j

WriteAckValue ==
    \A i \in 1..Len(observed) :
       (observed[i].type = "Ack" /\ observed[i].cmd \in Writes)
          => observed[i].val = observed[i].cmd

ReadsReturnRequestedWrites ==
    \A i \in 1..Len(observed) :
       (observed[i].type = "Ack" /\ observed[i].cmd \in Reads)
          => \/ observed[i].val = "nil"
             \/ /\ observed[i].val \in Writes
                /\ \E j \in 1..(i-1) : observed[j] = ReqEvent(observed[i].val)

\* Liveness: all replicas eventually terminate
Termination == <>(\A r \in Replicas : pc[r] = "Done")

=============================================================================