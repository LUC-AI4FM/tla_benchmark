---------------------------- MODULE Sailfish ----------------------------
(***************************************************************************)
(* High-level specification of the Sailfish and Sailfish++ DAG-based      *)
(* consensus algorithms.                                                  *)
(*                                                                         *)
(* Nodes build a DAG of vertices, one vertex per node per round. A vertex  *)
(* of round r references at least a quorum of vertices of round r-1. Each  *)
(* round has a designated leader. A vertex of round r+1 that references    *)
(* the leader vertex of round r counts as a vote for that leader vertex.   *)
(* A node that times out waiting for the leader vertex of round r sends a  *)
(* no-vote for round r, and its round r+1 vertex then does not reference   *)
(* that leader vertex. The leader vertex of round r+1 must either          *)
(* reference the leader vertex of round r or carry a quorum certificate of *)
(* no-votes for round r. A leader vertex is committed once a quorum of     *)
(* round r+1 vertices vote for it. Committing it also orders the earlier   *)
(* uncommitted leader vertices that are reachable from it.                 *)
(*                                                                         *)
(* Byzantine behaviour is constrained. Vertices are disseminated with      *)
(* reliable broadcast, so Byzantine nodes cannot equivocate: there is at   *)
(* most one vertex per (node, round). Every vertex must also pass the      *)
(* quorum checks that correct nodes perform before accepting it. So        *)
(* Byzantine nodes can only create protocol-conforming vertices, but they  *)
(* may choose their edges arbitrarily among the existing ones. They may    *)
(* also send no-votes arbitrarily, including no-votes for leaders they     *)
(* voted for. Reliable broadcast guarantees eventual delivery of every     *)
(* vertex to every node. At this level of abstraction, the DAG is          *)
(* therefore modeled as a single global set of vertices.                  *)
(*                                                                         *)
(* Sailfish and Sailfish++ share the same abstract DAG, vote and commit    *)
(* structure, which is what this module captures.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,      \* set of all nodes
    Byz,        \* set of Byzantine nodes
    Q,          \* quorum size (e.g. 2f+1 with n = 3f+1)
    MaxRound,   \* bound on the number of rounds
    GST,        \* first round after global stabilization time
    Leader(_)   \* Leader(r) is the leader of round r

ASSUME
    /\ Byz \subseteq Nodes
    /\ Q \in Nat \ {0}
    /\ MaxRound \in Nat \ {0}
    /\ GST \in Nat
    /\ \A r \in 1..MaxRound : Leader(r) \in Nodes
    /\ 2 * Q > Cardinality(Nodes) + Cardinality(Byz)   \* quorum intersection in a correct node
    /\ Cardinality(Nodes) - Cardinality(Byz) >= Q      \* correct nodes alone form a quorum

VARIABLES
    vs,             \* set of vertices in the (reliably broadcast) DAG
    round,          \* round[n]: highest round in which correct node n created a vertex
    noVotes,        \* set of pairs <<n, r>>: node n sent a no-vote for round r
    log,            \* log[n]: sequence of rounds of delivered (ordered) leader vertices
    lastCommitted   \* lastCommitted[n]: round of the last leader committed by n

vars == <<vs, round, noVotes, log, lastCommitted>>

Correct == Nodes \ Byz

Rounds == 0..MaxRound

Vertex == [source : Nodes, round : Rounds, edges : SUBSET Nodes]

-----------------------------------------------------------------------------
(* Helper operators *)

VerticesAt(r) == {v \in vs : v.round = r}

SourcesAt(r) == {v.source : v \in VerticesAt(r)}

HasVertex(n, r) == n \in SourcesAt(r)

LeaderVertexPresent(r) == r >= 1 /\ HasVertex(Leader(r), r)

LeaderVertex(r) == CHOOSE v \in VerticesAt(r) : v.source = Leader(r)

IsLeaderVertex(v) == v.round >= 1 /\ v.source = Leader(v.round)

NoVoteCert(r) == Cardinality({m \in Nodes : <<m, r>> \in noVotes}) >= Q

Votes(r) == {v \in VerticesAt(r + 1) : Leader(r) \in v.edges}

\* A round is synchronous if it is after GST and its leader is correct
SyncRound(r) == r >= GST /\ Leader(r) \in Correct

\* Path from vertex v down to vertex w in the DAG
RECURSIVE Reach(_, _)
Reach(v, w) ==
    IF v = w THEN TRUE
    ELSE IF v.round <= w.round THEN FALSE
    ELSE \E u \in VerticesAt(v.round - 1) :
            /\ u.source \in v.edges
            /\ Reach(u, w)

\* Rounds of leader vertices ordered when committing leader vertex v,
\* given that leaders up to round lo were already ordered (increasing order).
RECURSIVE LeaderChain(_, _)
LeaderChain(v, lo) ==
    LET prevs == {u \in vs : /\ IsLeaderVertex(u)
                             /\ u.round > lo
                             /\ u.round < v.round
                             /\ Reach(v, u)}
    IN IF prevs = {}
          THEN <<v.round>>
          ELSE LET p == CHOOSE u \in prevs :
                            \A u2 \in prevs : u2.round <= u.round
               IN Append(LeaderChain(p, lo), v.round)

\* Checks that every node performs before accepting a vertex
\* (enforced through reliable broadcast).
ValidVertex(n, r, E) ==
    /\ E \subseteq SourcesAt(r - 1)
    /\ Cardinality(E) >= Q
    /\ (r > 1 /\ n = Leader(r)) => (Leader(r - 1) \in E \/ NoVoteCert(r - 1))

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
(* Initial state: genesis vertices of round 0 for all nodes *)

Init ==
    /\ vs = {[source |-> n, round |-> 0, edges |-> {}] : n \in Nodes}
    /\ round = [n \in Nodes |-> 0]
    /\ noVotes = {}
    /\ log = [n \in Nodes |-> <<>>]
    /\ lastCommitted = [n \in Nodes |-> 0]

-----------------------------------------------------------------------------
(* Correct nodes *)

\* Correct node n creates its vertex for the next round. It references all
\* round r-1 vertices it has, except the leader vertex if it no-voted.
\* A correct node waits for the leader vertex of the previous round unless
\* it timed out (sent a no-vote).
CorrectPropose(n) ==
    LET r == round[n] + 1
        E == IF r > 1 /\ <<n, r - 1>> \in noVotes
                THEN SourcesAt(r - 1) \ {Leader(r - 1)}
                ELSE SourcesAt(r - 1)
    IN /\ r <= MaxRound
       /\ r > 1 => (LeaderVertexPresent(r - 1) \/ <<n, r - 1>> \in noVotes)
       /\ ValidVertex(n, r, E)
       /\ vs' = vs \cup {[source |-> n, round |-> r, edges |-> E]}
       /\ round' = [round EXCEPT ![n] = r]
       /\ UNCHANGED <<noVotes, log, lastCommitted>>

\* Correct node n times out waiting for the leader vertex of its current
\* round and sends a no-vote. In synchronous rounds (after GST with a
\* correct leader) the leader vertex arrives in time, so no timeout occurs.
CorrectTimeout(n) ==
    LET r == round[n]
    IN /\ r >= 1
       /\ ~SyncRound(r)
       /\ ~LeaderVertexPresent(r)
       /\ <<n, r>> \notin noVotes
       /\ noVotes' = noVotes \cup {<<n, r>>}
       /\ UNCHANGED <<vs, round, log, lastCommitted>>

\* Correct node n commits the leader vertex of round r once a quorum of
\* round r+1 vertices vote for it. It then delivers the chain of earlier
\* uncommitted leader vertices that are reachable from it.
CorrectCommit(n, r) ==
    /\ r > lastCommitted[n]
    /\ r < MaxRound
    /\ LeaderVertexPresent(r)
    /\ Cardinality(Votes(r)) >= Q
    /\ log' = [log EXCEPT ![n] = @ \o LeaderChain(LeaderVertex(r), lastCommitted[n])]
    /\ lastCommitted' = [lastCommitted EXCEPT ![n] = r]
    /\ UNCHANGED <<vs, round, noVotes>>

CorrectStep(n) ==
    \/ CorrectPropose(n)
    \/ CorrectTimeout(n)
    \/ \E r \in 1..MaxRound : CorrectCommit(n, r)

-----------------------------------------------------------------------------
(* Byzantine nodes: no equivocation, only protocol-conforming vertices *)

ByzPropose(n) ==
    \E r \in 1..MaxRound, E \in SUBSET Nodes :
        /\ ~HasVertex(n, r)                 \* reliable broadcast: no equivocation
        /\ ValidVertex(n, r, E)             \* must pass quorum checks
        /\ vs' = vs \cup {[source |-> n, round |-> r, edges |-> E]}
        /\ UNCHANGED <<round, noVotes, log, lastCommitted>>

ByzNoVote(n) ==
    \E r \in 1..MaxRound :
        /\ <<n, r>> \notin noVotes
        /\ noVotes' = noVotes \cup {<<n, r>>}
        /\ UNCHANGED <<vs, round, log, lastCommitted>>

ByzStep(n) == ByzPropose(n) \/ ByzNoVote(n)

-----------------------------------------------------------------------------

Next ==
    \/ \E n \in Correct : CorrectStep(n)
    \/ \E n \in Byz : ByzStep(n)

Fairness ==
    \A n \in Correct :
        /\ WF_vars(CorrectPropose(n))
        /\ WF_vars(CorrectTimeout(n))
        /\ WF_vars(\E r \in 1..MaxRound : CorrectCommit(n, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ vs \subseteq Vertex
    /\ round \in [Nodes -> Rounds]
    /\ noVotes \subseteq (Nodes \X Rounds)
    /\ log \in [Nodes -> Seq(1..MaxRound)]
    /\ lastCommitted \in [Nodes -> Rounds]

\* Reliable broadcast prevents equivocation
NoEquivocation ==
    \A v, w \in vs : (v.source = w.source /\ v.round = w.round) => v = w

\* Safety: logs delivered by correct nodes are consistent (one is a prefix of the other)
Agreement ==
    \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* Liveness: after GST, leaders of synchronous rounds eventually appear in
\* the logs of all correct nodes.
Liveness ==
    \A r \in 1..(MaxRound - 1) :
        SyncRound(r) =>
            \A n \in Correct :
                <>(\E i \in 1..Len(log[n]) : log[n][i] = r)

THEOREM Spec => [](TypeOK /\ NoEquivocation /\ Agreement)
THEOREM Spec => Liveness
=============================================================================