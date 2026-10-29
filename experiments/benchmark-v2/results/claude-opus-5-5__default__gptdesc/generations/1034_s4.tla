---------------------------- MODULE SailfishBounded3 ----------------------------
(***************************************************************************)
(* A small bounded configuration of the Sailfish DAG-based BFT protocol:  *)
(* three nodes, one of which (n3) is Byzantine.  Vertices are disseminated *)
(* by reliable broadcast, so there is no equivocation.  A vertex of round  *)
(* r > 1 must reference a quorum of round r-1 vertices.  It must also      *)
(* either reference the leader vertex of round r-1 or be justified by a    *)
(* no-vote certificate (NVC) for round r-1.                                 *)
(*                                                                         *)
(* A leader vertex of round r is committed when a quorum of round r+1      *)
(* vertices references it.  Committing a leader also orders, Bullshark     *)
(* style, the chain of earlier uncommitted leaders that it reaches.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxRound

ASSUME MaxRound \in Nat /\ MaxRound >= 1

(***************************************************************************)
(* Concrete node sets                                                      *)
(***************************************************************************)
N == {"n1", "n2", "n3"}     \* all nodes
B == {"n3"}                 \* Byzantine nodes
P == N \ B                  \* correct (non-faulty) nodes

(***************************************************************************)
(* Quorum and blocking-set predicates.                                     *)
(* This is a Byzantine quorum system for this configuration: every quorum  *)
(* contains all correct nodes, so any two quorums intersect in a correct   *)
(* node.  A blocking set is a set that intersects every quorum, which      *)
(* means it contains a correct node.                                       *)
(***************************************************************************)
IsQuorum(Q)    == Q \subseteq N /\ {"n1", "n2"} \subseteq Q
IsBlocking(S)  == S \subseteq N /\ \A Q \in SUBSET N : IsQuorum(Q) => Q \cap S # {}

(***************************************************************************)
(* Leader schedule and global stabilization time                           *)
(***************************************************************************)
Leader(r) == CASE r % 3 = 1 -> "n1"
             []   r % 3 = 2 -> "n2"
             []   OTHER     -> "n3"

GST == 3   \* from round GST on, correct nodes do not time out on correct leaders

VARIABLES
    round,          \* round[p]: the round in which correct node p creates its next vertex
    vertices,       \* all vertices reliably broadcast so far
    dag,            \* dag[p]: vertices delivered by correct node p
    noVotes,        \* no-vote messages [node, round]
    log,            \* log[p]: sequence of committed leader rounds at p
    lastCommitted   \* lastCommitted[p]: round of last committed leader at p

vars == <<round, vertices, dag, noVotes, log, lastCommitted>>

Vertex == [node : N, round : 1..MaxRound, edges : SUBSET N]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
VerticesOf(S, r) == {v \in S : v.round = r}
NodesOf(S)       == {v.node : v \in S}
IsLeaderVertex(v) == v.node = Leader(v.round)
NoVoters(r)      == {nv.node : nv \in {x \in noVotes : x.round = r}}
HasNVC(r)        == IsQuorum(NoVoters(r))

\* Round-1 vertices reference the (implicit) genesis vertices of all nodes.
ValidEdges(S, r, E) ==
    IF r = 1
    THEN E = N
    ELSE /\ IsQuorum(E)
         /\ E \subseteq NodesOf(VerticesOf(S, r - 1))
         /\ (Leader(r - 1) \in E \/ HasNVC(r - 1))

\* Vertices of D reachable from the set S, with S included.
RECURSIVE Reachable(_, _)
Reachable(D, S) ==
    LET next == {u \in D : \E w \in S : w.round = u.round + 1 /\ u.node \in w.edges}
    IN  IF next \subseteq S THEN S ELSE Reachable(D, S \cup next)

\* Order the chain of uncommitted leaders, with rounds > last, that ends in l.
RECURSIVE OrderFrom(_, _, _)
OrderFrom(D, l, last) ==
    LET prev == {v \in Reachable(D, {l}) :
                    IsLeaderVertex(v) /\ v.round > last /\ v.round < l.round}
    IN  IF prev = {}
        THEN <<l.round>>
        ELSE OrderFrom(D, CHOOSE v \in prev : \A w \in prev : w.round <= v.round, last)
             \o <<l.round>>

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ round = [p \in P |-> 1]
    /\ vertices = {}
    /\ dag = [p \in P |-> {}]
    /\ noVotes = {}
    /\ log = [p \in P |-> <<>>]
    /\ lastCommitted = [p \in P |-> 0]

(***************************************************************************)
(* Correct-node actions                                                    *)
(***************************************************************************)
CreateVertex(p) ==
    LET r == round[p]
        E == IF r = 1 THEN N ELSE NodesOf(VerticesOf(dag[p], r - 1))
        v == [node |-> p, round |-> r, edges |-> E]
    IN  /\ r <= MaxRound
        /\ ~\E w \in vertices : w.node = p /\ w.round = r
        /\ ValidEdges(dag[p], r, E)
        /\ vertices' = vertices \cup {v}
        /\ dag' = [dag EXCEPT ![p] = @ \cup {v}]
        /\ round' = [round EXCEPT ![p] = r + 1]
        /\ UNCHANGED <<noVotes, log, lastCommitted>>

\* Timeout waiting for the leader vertex of round[p]-1: send a no-vote.
Timeout(p) ==
    LET r == round[p] IN
    /\ 1 < r /\ r <= MaxRound
    /\ {v \in VerticesOf(dag[p], r - 1) : IsLeaderVertex(v)} = {}
    /\ [node |-> p, round |-> r - 1] \notin noVotes
    /\ \/ r - 1 < GST
       \/ Leader(r - 1) \in B
       \/ IsBlocking(NoVoters(r - 1))
    /\ noVotes' = noVotes \cup {[node |-> p, round |-> r - 1]}
    /\ UNCHANGED <<round, vertices, dag, log, lastCommitted>>

\* Causally-ordered delivery of a reliably broadcast vertex.
Deliver(p) ==
    \E v \in vertices \ dag[p] :
        /\ \/ v.round = 1
           \/ \A q \in v.edges : \E w \in dag[p] : w.node = q /\ w.round = v.round - 1
        /\ dag' = [dag EXCEPT ![p] = @ \cup {v}]
        /\ UNCHANGED <<round, vertices, noVotes, log, lastCommitted>>

Commit(p) ==
    \E l \in dag[p] :
        /\ IsLeaderVertex(l)
        /\ l.round > lastCommitted[p]
        /\ IsQuorum({w.node : w \in {x \in VerticesOf(dag[p], l.round + 1) :
                                                 l.node \in x.edges}})
        /\ log' = [log EXCEPT ![p] = @ \o OrderFrom(dag[p], l, lastCommitted[p])]
        /\ lastCommitted' = [lastCommitted EXCEPT ![p] = l.round]
        /\ UNCHANGED <<round, vertices, dag, noVotes>>

(***************************************************************************)
(* Byzantine actions                                                       *)
(* Reliable broadcast prevents equivocation, and correct nodes only accept *)
(* valid vertices.                                                         *)
(***************************************************************************)
ByzVertex(b) ==
    \E r \in 1..MaxRound, E \in SUBSET N :
        /\ ~\E w \in vertices : w.node = b /\ w.round = r
        /\ ValidEdges(vertices, r, E)
        /\ vertices' = vertices \cup {[node |-> b, round |-> r, edges |-> E]}
        /\ UNCHANGED <<round, dag, noVotes, log, lastCommitted>>

ByzNoVote(b) ==
    \E r \in 1..MaxRound :
        /\ [node |-> b, round |-> r] \notin noVotes
        /\ noVotes' = noVotes \cup {[node |-> b, round |-> r]}
        /\ UNCHANGED <<round, vertices, dag, log, lastCommitted>>

(***************************************************************************)
(* Next-state relation and specifications                                  *)
(***************************************************************************)
Next ==
    \/ \E p \in P : CreateVertex(p) \/ Timeout(p) \/ Deliver(p) \/ Commit(p)
    \/ \E b \in B : ByzVertex(b) \/ ByzNoVote(b)

Fairness ==
    \A p \in P :
        /\ WF_vars(CreateVertex(p))
        /\ WF_vars(Timeout(p))
        /\ WF_vars(Deliver(p))
        /\ WF_vars(Commit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Terminating variant: once all correct nodes have finished, stutter.
\* This variant prevents spurious deadlock reports.
Done == \A p \in P : round[p] > MaxRound

Terminating == Done /\ UNCHANGED vars

TerminatingNext == Next \/ Terminating

TerminatingSpec == Init /\ [][TerminatingNext]_vars /\ Fairness

(***************************************************************************)
(* State constraint bounding explored rounds of non-faulty nodes           *)
(***************************************************************************)
StateConstraint == \A p \in P : round[p] <= MaxRound + 1

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
    /\ round \in [P -> 1..(MaxRound + 1)]
    /\ vertices \subseteq Vertex
    /\ dag \in [P -> SUBSET Vertex]
    /\ \A p \in P : dag[p] \subseteq vertices
    /\ noVotes \subseteq [node : N, round : 1..MaxRound]
    /\ log \in [P -> Seq(1..MaxRound)]
    /\ lastCommitted \in [P -> 0..MaxRound]

NoEquivocation ==
    \A v, w \in vertices : (v.node = w.node /\ v.round = w.round) => v = w

LogConsistency ==
    \A p, q \in P : IsPrefix(log[p], log[q]) \/ IsPrefix(log[q], log[p])

LogStrictlyIncreasing ==
    \A p \in P : \A i, j \in 1..Len(log[p]) : i < j => log[p][i] < log[p][j]

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>Done

(***************************************************************************)
(* Deliberately false predicates, used to obtain interesting               *)
(* counterexample executions from TLC.                                     *)
(***************************************************************************)
\* Violated when all correct nodes finish.
Falsy_NotAllDone == ~Done

\* Violated when a correct node commits something.
Falsy_NoCommit == \A p \in P : log[p] = <<>>

\* Violated when a correct node commits at least two leaders.
Falsy_ShortLogs == \A p \in P : Len(log[p]) < 2

\* Violated when a Byzantine leader's vertex is committed.
Falsy_NoByzantineLeaderCommitted ==
    \A p \in P : \A i \in 1..Len(log[p]) : Leader(log[p][i]) \notin B

\* Temporal: violated by executions in which all correct nodes finish.
Falsy_NeverAllDone == []~Done

\* Temporal: violated by executions that reach Done with a non-empty log.
Falsy_DoneWithoutCommit == [](Done => \A p \in P : log[p] = <<>>)

\* Temporal: violated by executions in which some log never grows.
Falsy_EventuallyAllCommitTwo == <>(\A p \in P : Len(log[p]) >= 2)

=============================================================================