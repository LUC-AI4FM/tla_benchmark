---- MODULE Sailfish ----
(***************************************************************************)
(* A high-level specification of the Sailfish and Sailfish++ DAG-based     *)
(* consensus protocols, with correct and Byzantine nodes.                  *)
(*                                                                         *)
(* Vertices are disseminated with reliable broadcast, so a Byzantine node  *)
(* cannot equivocate: each (round, author) pair identifies at most one     *)
(* vertex, and every correct node eventually delivers the same vertex.     *)
(* Correct nodes deliver a vertex only after delivering its causal history.*)
(* Byzantine nodes may only create vertices that conform to the protocol,  *)
(* because receivers check them. For example, a vertex needs strong edges  *)
(* to a quorum of vertices from the previous round. A Byzantine node's     *)
(* vertex may otherwise be arbitrary: any edge set and any NVC flag that   *)
(* passes the checks. A Byzantine node may also send no-vote messages      *)
(* freely.                                                                 *)
(*                                                                         *)
(* A vertex of round r that is created by the leader of r must either      *)
(* reference the leader of round r-1 or carry a no-vote certificate (NVC). *)
(* An NVC is a quorum of no-vote messages for round r-1. A correct node    *)
(* that times out on the leader of round r sends a no-vote for round r. If *)
(* it is not the next leader, it then omits the leader edge.               *)
(*                                                                         *)
(* A leader vertex is committed directly when a quorum of round r+1        *)
(* vertices references it. Earlier uncommitted leader vertices that are    *)
(* reachable from it are ordered first.                                    *)
(*                                                                         *)
(* Rounds >= GSTRound are synchronous. A correct node never times out on a *)
(* correct leader of a synchronous round.                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node,       \* set of all nodes
          Byz,        \* set of Byzantine nodes
          MaxRound,   \* bound on the number of rounds
          GSTRound,   \* first round that starts after GST
          Leader      \* Leader[r] is the leader of round r

Round == 1..MaxRound

ASSUME Byz \subseteq Node
ASSUME MaxRound \in Nat /\ MaxRound >= 1
ASSUME GSTRound \in Round
ASSUME Leader \in [Round -> Node]
ASSUME 3 * Cardinality(Byz) < Cardinality(Node)

Correct == Node \ Byz
N == Cardinality(Node)
F == (N - 1) \div 3
Q == N - F                       \* quorum size (2f+1 when n = 3f+1)

Vertex == [round : Round, author : Node, edges : SUBSET Node, nvc : BOOLEAN]

VARIABLES vertices,       \* all vertices reliably broadcast so far
          dag,            \* dag[n]: vertices delivered by node n
          noVote,         \* set of <<r, n>>: n sent a no-vote for leader of r
          log,            \* log[n]: sequence of ordered leader vertices
          lastCommitted   \* lastCommitted[n]: round of last committed leader

vars == <<vertices, dag, noVote, log, lastCommitted>>

---------------------------------------------------------------------------
(* Helpers *)

VerticesOf(S, r) == {v \in S : v.round = r}
AuthorsOf(S, r) == {v.author : v \in VerticesOf(S, r)}
LeaderVertex(S, r) == {v \in S : v.round = r /\ v.author = Leader[r]}
HasCreated(n, r) == \E v \in vertices : v.round = r /\ v.author = n
NoVotesFor(r) == {m \in Node : <<r, m>> \in noVote}
Votes(S, lv) == {v \in S : v.round = lv.round + 1 /\ lv.author \in v.edges}

(* Protocol-conforming vertex with respect to a view S (no equivocation). *)
ValidVertex(v, S) ==
  /\ ~HasCreated(v.author, v.round)
  /\ IF v.round = 1
       THEN v.edges = {} /\ v.nvc = FALSE
       ELSE /\ v.edges \subseteq AuthorsOf(S, v.round - 1)
            /\ Cardinality(v.edges) >= Q
            /\ (v.author = Leader[v.round] /\ Leader[v.round - 1] \notin v.edges)
                  => v.nvc
            /\ v.nvc => Cardinality(NoVotesFor(v.round - 1)) >= Q

(* w is reachable from u by following edges inside S *)
RECURSIVE Reachable(_, _, _)
Reachable(S, u, w) ==
  \/ u = w
  \/ /\ u.round > w.round
     /\ \E p \in S : /\ p.round = u.round - 1
                     /\ p.author \in u.edges
                     /\ Reachable(S, p, w)

(* Leader vertices of rounds in (low, r] reachable from cur, ordered by round *)
RECURSIVE LeaderChain(_, _, _, _)
LeaderChain(S, cur, r, low) ==
  IF r <= low THEN << >>
  ELSE IF \E l \in LeaderVertex(S, r) : Reachable(S, cur, l)
       THEN LET nxt == CHOOSE l \in LeaderVertex(S, r) : Reachable(S, cur, l)
            IN LeaderChain(S, nxt, r - 1, low) \o << nxt >>
       ELSE LeaderChain(S, cur, r - 1, low)

---------------------------------------------------------------------------
(* Initialization *)

Init ==
  /\ vertices = {}
  /\ dag = [n \in Node |-> {}]
  /\ noVote = {}
  /\ log = [n \in Node |-> << >>]
  /\ lastCommitted = [n \in Node |-> 0]

---------------------------------------------------------------------------
(* Correct node actions *)

CorrectEdges(n, r) ==
  AuthorsOf(dag[n], r - 1) \
    (IF <<r - 1, n>> \in noVote /\ n # Leader[r] THEN {Leader[r - 1]} ELSE {})

CreateVertex(n) ==
  \E r \in Round :
    /\ ~HasCreated(n, r)
    /\ (r = 1 \/ HasCreated(n, r - 1))
    /\ (r > 1 => (Leader[r - 1] \in AuthorsOf(dag[n], r - 1)
                    \/ <<r - 1, n>> \in noVote))
    /\ LET v == IF r = 1
                  THEN [round |-> 1, author |-> n, edges |-> {}, nvc |-> FALSE]
                  ELSE [round |-> r, author |-> n,
                        edges |-> CorrectEdges(n, r),
                        nvc |-> (n = Leader[r]
                                  /\ Leader[r - 1] \notin CorrectEdges(n, r))]
       IN /\ ValidVertex(v, dag[n])
          /\ vertices' = vertices \cup {v}
          /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<noVote, log, lastCommitted>>

Timeout(n) ==
  \E r \in Round :
    /\ r < MaxRound
    /\ HasCreated(n, r)
    /\ ~HasCreated(n, r + 1)
    /\ <<r, n>> \notin noVote
    /\ LeaderVertex(dag[n], r) = {}
    /\ ~(r >= GSTRound /\ Leader[r] \in Correct)   \* no timeouts after GST
    /\ noVote' = noVote \cup {<<r, n>>}
    /\ UNCHANGED <<vertices, dag, log, lastCommitted>>

Receive(n) ==
  \E v \in vertices \ dag[n] :
    /\ \A a \in v.edges :
         \E p \in dag[n] : p.round = v.round - 1 /\ p.author = a
    /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<vertices, noVote, log, lastCommitted>>

Commit(n) ==
  \E r \in Round :
    /\ r > lastCommitted[n]
    /\ \E lv \in LeaderVertex(dag[n], r) :
         /\ Cardinality(Votes(dag[n], lv)) >= Q
         /\ log' = [log EXCEPT ![n] =
                      @ \o LeaderChain(dag[n], lv, r - 1, lastCommitted[n])
                        \o << lv >>]
         /\ lastCommitted' = [lastCommitted EXCEPT ![n] = r]
    /\ UNCHANGED <<vertices, dag, noVote>>

---------------------------------------------------------------------------
(* Byzantine node actions *)

ByzCreate ==
  \E b \in Byz, r \in Round, E \in SUBSET Node, nv \in BOOLEAN :
    LET v == [round |-> r, author |-> b, edges |-> E, nvc |-> nv]
    IN /\ ValidVertex(v, vertices)
       /\ vertices' = vertices \cup {v}
       /\ UNCHANGED <<dag, noVote, log, lastCommitted>>

ByzNoVote ==
  \E b \in Byz, r \in Round :
    /\ <<r, b>> \notin noVote
    /\ noVote' = noVote \cup {<<r, b>>}
    /\ UNCHANGED <<vertices, dag, log, lastCommitted>>

---------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
  \/ \E n \in Correct :
       \/ CreateVertex(n)
       \/ Timeout(n)
       \/ Receive(n)
       \/ Commit(n)
  \/ ByzCreate
  \/ ByzNoVote

Fairness ==
  \A n \in Correct :
    /\ WF_vars(CreateVertex(n))
    /\ WF_vars(Timeout(n))
    /\ WF_vars(Receive(n))
    /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ vertices \subseteq Vertex
  /\ dag \in [Node -> SUBSET Vertex]
  /\ noVote \subseteq (Round \X Node)
  /\ log \in [Node -> Seq(Vertex)]
  /\ lastCommitted \in [Node -> 0..MaxRound]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
  \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

InLog(n, r) ==
  \E i \in 1..Len(log[n]) :
    log[n][i].round = r /\ log[n][i].author = Leader[r]

(* After GST, leaders of synchronous rounds are eventually in correct logs. *)
Liveness ==
  \A r \in Round : \A n \in Correct :
    (r >= GSTRound /\ r < MaxRound /\ Leader[r] \in Correct) => <>InLog(n, r)

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => Liveness
====