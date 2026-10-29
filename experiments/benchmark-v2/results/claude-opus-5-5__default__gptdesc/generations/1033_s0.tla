------------------------------ MODULE Sailfish ------------------------------
(***************************************************************************)
(* High-level specification of the Sailfish and Sailfish++ DAG-based       *)
(* consensus algorithms. Nodes are either correct or Byzantine.            *)
(*                                                                         *)
(* Vertices are disseminated with reliable broadcast. As a result,         *)
(* Byzantine nodes cannot equivocate: each node has at most one vertex per *)
(* round, and every node eventually sees the same vertex. Correct nodes    *)
(* check every delivered vertex for validity (for example, quorum checks), *)
(* so Byzantine nodes can only create protocol-conforming vertices.        *)
(* Their freedom is limited to:                                            *)
(*   - choosing which valid quorum of previous-round vertices to reference;*)
(*   - not referencing the previous leader, even in synchronous rounds;    *)
(*   - creating vertices out of order, late, or never;                     *)
(*   - sending no-vote messages arbitrarily.                               *)
(*                                                                         *)
(* Because no node equivocates, a vertex is uniquely identified by its     *)
(* creator and round. The DAG is therefore modeled as a single global set  *)
(* of vertices.                                                            *)
(*                                                                         *)
(* Commit rule (Sailfish / Sailfish++): the leader vertex of round r is    *)
(* committed once 2f+1 vertices of round r+1 reference it. When a leader   *)
(* is committed, the node first orders the uncommitted previous leaders    *)
(* reachable from it, recursively. A leader vertex of round r that does    *)
(* not reference the leader of round r-1 must carry a no-vote certificate *)
(* (2f+1 no-votes for round r-1).                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,       \* set of all nodes
    Byz,        \* set of Byzantine nodes
    MaxRound,   \* bound on the number of rounds
    Leader,     \* Leader[r] is the leader of round r
    GST         \* first round after global stabilization time

ASSUME Byz \subseteq Node
ASSUME MaxRound \in Nat /\ MaxRound >= 1
ASSUME Leader \in [1..MaxRound -> Node]
ASSUME GST \in 1..MaxRound

Correct == Node \ Byz
N == Cardinality(Node)
F == (N - 1) \div 3
QuorumSize == 2 * F + 1

ASSUME Cardinality(Byz) <= F

Rounds == 1..MaxRound

Vertices == [node : Node, rnd : Rounds, edges : SUBSET Node, nvc : BOOLEAN]

VARIABLES
    dag,      \* set of vertices delivered via reliable broadcast
    round,    \* round[n]: last round in which correct node n created a vertex
    noVote,   \* noVote[r]: nodes that sent a no-vote for the leader of round r
    log       \* log[n]: sequence of leader rounds delivered by correct node n

vars == <<dag, round, noVote, log>>

---------------------------------------------------------------------------
(* Helper definitions *)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

HasVertex(m, r) == \E v \in dag : v.node = m /\ v.rnd = r

VertexOf(m, r) == CHOOSE v \in dag : v.node = m /\ v.rnd = r

\* A round is synchronous if it is after GST and its leader is correct.
Synchronous(r) == r >= GST /\ Leader[r] \notin Byz

\* Valid edge sets: round-1 vertices have no parents. Later vertices
\* reference a quorum of existing vertices from the previous round.
ValidEdges(E, r) ==
    IF r = 1 THEN E = {}
    ELSE /\ Cardinality(E) >= QuorumSize
         /\ \A m \in E : HasVertex(m, r - 1)

\* A no-vote certificate for round r is available given voter set S.
HasNVC(S) == Cardinality(S) >= QuorumSize

\* Path in the DAG from vertex v to the vertex of node m in round r2.
RECURSIVE Reaches(_, _, _)
Reaches(v, m, r2) ==
    IF v.rnd = r2 THEN v.node = m
    ELSE IF v.rnd < r2 THEN FALSE
    ELSE \E e \in v.edges : Reaches(VertexOf(e, v.rnd - 1), m, r2)

\* Number of round r+1 vertices that reference the leader of round r.
VoteCount(r) ==
    Cardinality({ m \in Node :
        HasVertex(m, r + 1) /\ Leader[r] \in VertexOf(m, r + 1).edges })

LastCommitted(n) == IF log[n] = << >> THEN 0 ELSE log[n][Len(log[n])]

\* Uncommitted leaders (rounds > lo) reachable from vertex v, ordered by
\* increasing round and computed recursively.
RECURSIVE LeaderChain(_, _)
LeaderChain(v, lo) ==
    LET cands == { r \in (lo + 1)..(v.rnd - 1) :
                     HasVertex(Leader[r], r) /\ Reaches(v, Leader[r], r) }
    IN IF cands = {} THEN << >>
       ELSE LET m == Max(cands)
            IN LeaderChain(VertexOf(Leader[m], m), lo) \o << m >>

---------------------------------------------------------------------------
(* Initialization *)

Init ==
    /\ dag = {}
    /\ round = [n \in Correct |-> 0]
    /\ noVote = [r \in Rounds |-> {}]
    /\ log = [n \in Correct |-> << >>]

---------------------------------------------------------------------------
(* Correct node actions *)

\* A correct node creates its vertex for the next round. In a synchronous
\* previous round, it waits for the leader vertex and references it. If it
\* does not reference the previous leader, it sends a no-vote. A leader
\* vertex without the previous leader must carry a no-vote certificate.
CorrectCreate(n) ==
    /\ round[n] < MaxRound
    /\ LET r == round[n] + 1 IN
         /\ \E E \in SUBSET Node :
              /\ ValidEdges(E, r)
              /\ (r > 1 /\ Synchronous(r - 1)) => Leader[r - 1] \in E
              /\ LET skip == r > 1 /\ Leader[r - 1] \notin E IN
                   /\ (n = Leader[r] /\ skip) =>
                          HasNVC(noVote[r - 1] \cup {n})
                   /\ dag' = dag \cup
                        {[node |-> n, rnd |-> r, edges |-> E,
                          nvc |-> (skip /\ n = Leader[r])]}
                   /\ noVote' = IF skip
                                THEN [noVote EXCEPT ![r - 1] = @ \cup {n}]
                                ELSE noVote
         /\ round' = [round EXCEPT ![n] = r]
    /\ UNCHANGED log

\* A correct node commits the leader of round r once it has 2f+1 votes.
\* It first delivers the uncommitted leaders reachable from that leader.
CorrectCommit(n, r) ==
    /\ r \in 1..(MaxRound - 1)
    /\ r > LastCommitted(n)
    /\ HasVertex(Leader[r], r)
    /\ VoteCount(r) >= QuorumSize
    /\ log' = [log EXCEPT ![n] =
                 @ \o LeaderChain(VertexOf(Leader[r], r), LastCommitted(n))
                   \o << r >>]
    /\ UNCHANGED <<dag, round, noVote>>

CorrectStep(n) ==
    \/ CorrectCreate(n)
    \/ \E r \in Rounds : CorrectCommit(n, r)

---------------------------------------------------------------------------
(* Byzantine node actions *)

\* A Byzantine node creates at most one vertex per round (reliable
\* broadcast prevents equivocation). It may do so in any order, and the
\* vertex must pass the validity checks of correct nodes. It is not
\* required to reference the previous leader, even in synchronous rounds.
ByzCreate(b) ==
    /\ \E r \in Rounds :
         /\ ~HasVertex(b, r)
         /\ \E E \in SUBSET Node :
              /\ ValidEdges(E, r)
              /\ LET skip == r > 1 /\ Leader[r - 1] \notin E IN
                   /\ (b = Leader[r] /\ skip) => HasNVC(noVote[r - 1])
                   /\ dag' = dag \cup
                        {[node |-> b, rnd |-> r, edges |-> E,
                          nvc |-> (skip /\ b = Leader[r])]}
    /\ UNCHANGED <<round, noVote, log>>

\* A Byzantine node sends an arbitrary no-vote.
ByzNoVote(b) ==
    /\ \E r \in Rounds :
         /\ b \notin noVote[r]
         /\ noVote' = [noVote EXCEPT ![r] = @ \cup {b}]
    /\ UNCHANGED <<dag, round, log>>

ByzStep(b) == ByzCreate(b) \/ ByzNoVote(b)

---------------------------------------------------------------------------
(* Next-state relation and specification *)

\* Stuttering once every correct node has reached the round bound,
\* which avoids spurious deadlock reports.
Terminating ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Correct : CorrectStep(n)
    \/ \E b \in Byz : ByzStep(b)
    \/ Terminating

Fairness ==
    \A n \in Correct :
        /\ WF_vars(CorrectCreate(n))
        /\ WF_vars(\E r \in Rounds : CorrectCommit(n, r))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ dag \subseteq Vertices
    /\ round \in [Correct -> 0..MaxRound]
    /\ noVote \in [Rounds -> SUBSET Node]
    /\ log \in [Correct -> Seq(Rounds)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* Safety: the delivered logs of correct nodes are consistent.
Agreement ==
    \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* Liveness: after GST, the leader of every synchronous round eventually
\* appears in the log of every correct node.
Liveness ==
    \A r \in 1..(MaxRound - 1) :
        Synchronous(r) =>
            \A n \in Correct :
                <>(\E i \in 1..Len(log[n]) : log[n][i] = r)

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => Liveness

=============================================================================