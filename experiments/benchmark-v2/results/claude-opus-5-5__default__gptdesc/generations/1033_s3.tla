------------------------------- MODULE Sailfish -------------------------------
(***************************************************************************)
(* High-level specification of the Sailfish and Sailfish++ DAG-based      *)
(* consensus protocols.                                                    *)
(*                                                                         *)
(* The system has correct and Byzantine nodes. Vertices are disseminated   *)
(* with reliable broadcast (RBC), so a Byzantine node cannot equivocate.   *)
(* It can create at most one vertex per round, and every vertex it creates *)
(* is delivered identically to all correct nodes. RBC validity and the     *)
(* quorum checks done by receivers also limit Byzantine nodes to creating  *)
(* protocol-conforming vertices:                                           *)
(*   - a round-r vertex (r > 1) has strong edges to at least a quorum      *)
(*     (n - f) of round r-1 vertices, and                                  *)
(*   - it either references the leader vertex of round r-1 or carries a    *)
(*     no-vote certificate (a quorum of no-votes) for round r-1.           *)
(* Byzantine nodes may still send no-votes arbitrarily and may choose      *)
(* their edges and timing freely within these limits.                      *)
(*                                                                         *)
(* Sailfish and Sailfish++ share this high-level DAG structure and commit  *)
(* rule. A leader vertex of round r is committed directly once a quorum of *)
(* round r+1 vertices reference it. Earlier uncommitted leaders that are   *)
(* reachable from it are then ordered before it (indirect commit).         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,      \* set of all nodes
    Byz,        \* set of Byzantine nodes
    MaxRound,   \* bound on the number of rounds
    Leader,     \* Leader[r] is the leader of round r
    GST         \* first round after the global stabilization time

Rounds  == 1..MaxRound
Correct == Nodes \ Byz
F       == (Cardinality(Nodes) - 1) \div 3
Quorum  == Cardinality(Nodes) - F

ASSUME /\ Byz \subseteq Nodes
       /\ Cardinality(Byz) <= F
       /\ MaxRound \in Nat \ {0}
       /\ Leader \in [Rounds -> Nodes]
       /\ GST \in Rounds

(* A vertex is identified by (src, rnd). edges holds the sources of the   *)
(* round rnd-1 vertices it references. nvc says whether it carries a      *)
(* no-vote certificate for round rnd-1.                                   *)
Vertices == [src : Nodes, rnd : Rounds, edges : SUBSET Nodes, nvc : BOOLEAN]

VARIABLES
    sent,       \* vertices reliably broadcast so far
    dag,        \* dag[n] : vertices delivered to correct node n
    curRound,   \* curRound[n] : round of the last vertex created by correct n
    noVotes,    \* noVotes[r] : nodes that sent a no-vote for leader of r
    log         \* log[n] : sequence of rounds whose leader vertex n ordered

vars == <<sent, dag, curRound, noVotes, log>>

-----------------------------------------------------------------------------
(* Helper operators *)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

LeaderVertex(D, r) == {v \in D : v.rnd = r /\ v.src = Leader[r]}

Parents(D, S) ==
    {w \in D : \E u \in S : w.rnd = u.rnd - 1 /\ w.src \in u.edges}

RECURSIVE Ancestors(_, _)
Ancestors(D, S) ==
    IF S = {} THEN {} ELSE S \cup Ancestors(D, Parents(D, S))

Path(D, v, w) == w \in Ancestors(D, {v})

(* Ordering of leaders: starting from leader vertex v, order the reachable *)
(* uncommitted leaders (rounds > lo) in increasing round order.           *)
RECURSIVE Chain(_, _, _)
Chain(D, v, lo) ==
    LET prev == {r \in (lo + 1)..(v.rnd - 1) :
                    \E w \in LeaderVertex(D, r) : Path(D, v, w)}
    IN IF prev = {}
         THEN <<v.rnd>>
         ELSE LET r2 == Max(prev)
                  w  == CHOOSE x \in LeaderVertex(D, r2) : TRUE
              IN Chain(D, w, lo) \o <<v.rnd>>

LastCommitted(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
Init ==
    /\ sent = {}
    /\ dag = [n \in Correct |-> {}]
    /\ curRound = [n \in Correct |-> 0]
    /\ noVotes = [r \in Rounds |-> {}]
    /\ log = [n \in Correct |-> <<>>]

-----------------------------------------------------------------------------
(* Correct node actions *)

(* A correct node creates its vertex for the next round. It references all *)
(* round r-1 vertices it has delivered, which must be a quorum. If the     *)
(* round r-1 leader vertex is missing, it needs a no-vote certificate.    *)
(* After GST it waits for the vertex of a correct leader.                  *)
CreateVertex(n) ==
    LET r         == curRound[n] + 1
        P         == {v \in dag[n] : v.rnd = r - 1}
        E         == {v.src : v \in P}
        hasLeader == r > 1 /\ Leader[r - 1] \in E
        useNvc    == r > 1 /\ ~hasLeader
        v         == [src |-> n, rnd |-> r, edges |-> E, nvc |-> useNvc]
    IN /\ r <= MaxRound
       /\ (r > 1) => Cardinality(E) >= Quorum
       /\ (r > 1 /\ r - 1 >= GST /\ Leader[r - 1] \in Correct) => hasLeader
       /\ useNvc => Cardinality(noVotes[r - 1]) >= Quorum
       /\ sent' = sent \cup {v}
       /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
       /\ curRound' = [curRound EXCEPT ![n] = r]
       /\ UNCHANGED <<noVotes, log>>

(* Timeout: a correct node waiting in round r without the leader vertex   *)
(* sends a no-vote. Timeouts cannot fire for correct leaders after GST.   *)
SendNoVote(n) ==
    LET r == curRound[n]
    IN /\ r >= 1
       /\ n \notin noVotes[r]
       /\ LeaderVertex(dag[n], r) = {}
       /\ (r < GST \/ Leader[r] \in Byz)
       /\ noVotes' = [noVotes EXCEPT ![r] = @ \cup {n}]
       /\ UNCHANGED <<sent, dag, curRound, log>>

(* Reliable-broadcast delivery of a vertex once its causal history is      *)
(* already delivered.                                                      *)
Deliver(n, v) ==
    /\ v \in sent
    /\ v \notin dag[n]
    /\ \A w \in sent : (w.rnd = v.rnd - 1 /\ w.src \in v.edges) => w \in dag[n]
    /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<sent, curRound, noVotes, log>>

(* Direct commit of a leader vertex with a quorum of votes from the next   *)
(* round, plus indirect ordering of earlier reachable leaders.            *)
Commit(n) ==
    \E v \in dag[n] :
        /\ v.src = Leader[v.rnd]
        /\ v.rnd > LastCommitted(n)
        /\ Cardinality({w \in dag[n] : w.rnd = v.rnd + 1 /\ v.src \in w.edges})
              >= Quorum
        /\ log' = [log EXCEPT ![n] = @ \o Chain(dag[n], v, LastCommitted(n))]
        /\ UNCHANGED <<sent, dag, curRound, noVotes>>

-----------------------------------------------------------------------------
(* Byzantine node actions. Because of reliable broadcast they cannot       *)
(* equivocate and must create protocol-conforming vertices.               *)

ByzCreateVertex(b) ==
    \E r \in Rounds :
        /\ ~\E v \in sent : v.src = b /\ v.rnd = r
        /\ \E E \in SUBSET {w.src : w \in {x \in sent : x.rnd = r - 1}} :
            LET hasLeader == r > 1 /\ Leader[r - 1] \in E
                useNvc    == r > 1 /\ ~hasLeader
            IN /\ (r > 1) => Cardinality(E) >= Quorum
               /\ useNvc => Cardinality(noVotes[r - 1]) >= Quorum
               /\ sent' = sent \cup
                     {[src |-> b, rnd |-> r, edges |-> E, nvc |-> useNvc]}
        /\ UNCHANGED <<dag, curRound, noVotes, log>>

ByzNoVote(b) ==
    \E r \in Rounds :
        /\ b \notin noVotes[r]
        /\ noVotes' = [noVotes EXCEPT ![r] = @ \cup {b}]
        /\ UNCHANGED <<sent, dag, curRound, log>>

-----------------------------------------------------------------------------
CorrectNext(n) ==
    \/ CreateVertex(n)
    \/ SendNoVote(n)
    \/ \E v \in sent : Deliver(n, v)
    \/ Commit(n)

ByzNext(b) ==
    \/ ByzCreateVertex(b)
    \/ ByzNoVote(b)

Next ==
    \/ \E n \in Correct : CorrectNext(n)
    \/ \E b \in Byz : ByzNext(b)

Fairness ==
    \A n \in Correct :
        /\ WF_vars(CreateVertex(n))
        /\ WF_vars(SendNoVote(n))
        /\ WF_vars(\E v \in sent : Deliver(n, v))
        /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ sent \subseteq Vertices
    /\ dag \in [Correct -> SUBSET Vertices]
    /\ curRound \in [Correct -> 0..MaxRound]
    /\ noVotes \in [Rounds -> SUBSET Nodes]
    /\ log \in [Correct -> Seq(Rounds)]

(* Agreement: logs delivered by correct nodes are prefix-consistent. *)
Agreement ==
    \A n1, n2 \in Correct :
        IsPrefix(log[n1], log[n2]) \/ IsPrefix(log[n2], log[n1])

(* Liveness: after GST, the leader of every synchronous round with a       *)
(* correct leader is eventually in the log of every correct node. The last *)
(* round is excluded because there is no next round to vote for it.       *)
Liveness ==
    \A r \in GST..(MaxRound - 1) :
        (Leader[r] \in Correct) =>
            \A n \in Correct :
                <>(\E i \in 1..Len(log[n]) : log[n][i] = r)

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => Liveness
=============================================================================