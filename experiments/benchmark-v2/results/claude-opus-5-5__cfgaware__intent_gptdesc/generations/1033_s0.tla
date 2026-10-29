------------------------------- MODULE DAGBFT -------------------------------
(***************************************************************************)
(* High-level model of a round-based, leader-driven BFT protocol that      *)
(* builds a DAG of proposals (vertices) and linearizes committed leader    *)
(* vertices with a quorum/blocking-set decision rule.                      *)
(*                                                                         *)
(*  - A vertex is a pair <<node, round>>. Each node has at most one vertex *)
(*    per round, so no node, correct or Byzantine, can equivocate.         *)
(*  - Every vertex of round r > 1 references (has as children) vertices    *)
(*    of round r-1 only, and their authors form a quorum.                  *)
(*  - The decision on the leader vertex L of round r uses the round r+1   *)
(*    vertices in a node's causal history:                                 *)
(*      * a quorum of them reference L          ==> L is committed         *)
(*      * a blocking set of them do not         ==> L is skipped           *)
(*      * otherwise                             ==> undecided (log stops)  *)
(*    A quorum and a blocking set together hold more than |N| distinct     *)
(*    authors. One node has at most one vertex per round, so no two       *)
(*    histories can decide differently on L. Logs are therefore always    *)
(*    prefix-compatible.                                                   *)
(*  - Partial synchrony is abstracted by GST. In every round k > GST, a   *)
(*    correct node waits for and references the vertex of the correct      *)
(*    leader of round k-1.                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N            \* the set of nodes

VARIABLES
    vs,     \* set of vertices <<node, round>>
    es,     \* set of edges <<parent, child>>; the child is in the previous round
    round,  \* round[n] = last round in which node n proposed (0 = none yet)
    log     \* log[n] = linearized sequence of committed leader vertices

vars == <<vs, es, round, log>>

-----------------------------------------------------------------------------
(* Model parameters (defined, not configured)                              *)

MaxRound == 4
GST      == 2
Rounds   == 1..MaxRound

NumNodes == Cardinality(N)

\* A fixed enumeration of the nodes.
NodeSeq == CHOOSE f \in [1..NumNodes -> N] :
              \A i, j \in 1..NumNodes : i # j => f[i] # f[j]

\* Maximum number of Byzantine nodes: 3F < |N|
F == (NumNodes - 1) \div 3

Byz     == {NodeSeq[NumNodes - i + 1] : i \in 1..F}
Correct == N \ Byz

\* Distinguished leader of each round
Leader(r) == NodeSeq[((r - 1) % NumNodes) + 1]
LeaderVertex(r) == <<Leader(r), r>>

-----------------------------------------------------------------------------
(* Quorums and blocking sets (abstract threshold semantics)                *)

IsQuorum(S)   == S \subseteq N /\ Cardinality(S) >= NumNodes - F
IsBlocking(S) == S \subseteq N /\ Cardinality(S) >= F + 1

Authors(S) == {v[1] : v \in S}

-----------------------------------------------------------------------------
(* DAG helpers                                                             *)

Vertex == N \X Rounds

ChildrenIn(E, v) == {e[2] : e \in {x \in E : x[1] = v}}

RECURSIVE HistE(_, _)
\* Causal history of v (v included) w.r.t. edge set E
HistE(E, v) == {v} \cup UNION {HistE(E, c) : c \in ChildrenIn(E, v)}

\* Linearization of a causal history H, deciding leaders of rounds r .. maxR-1
RECURSIVE Lin(_, _, _, _)
Lin(E, H, r, maxR) ==
    IF r >= maxR THEN << >>
    ELSE
      LET L      == LeaderVertex(r)
          R1     == {w \in H : w[2] = r + 1}
          voters == Authors({w \in R1 : <<w, L>> \in E})
          others == Authors({w \in R1 : <<w, L>> \notin E})
      IN  IF IsQuorum(voters)
            THEN <<L>> \o Lin(E, H, r + 1, maxR)
          ELSE IF IsBlocking(others)
            THEN Lin(E, H, r + 1, maxR)
          ELSE << >>

Linearize(E, v) == Lin(E, HistE(E, v), 1, v[2])

\* Vertices of round k-1 (candidate children for a round-k vertex)
Prev(k) == {v \in vs : v[2] = k - 1}

\* Valid choice of children for a new round-k vertex
ValidChildren(k, Q) ==
    IF k = 1 THEN Q = {}
    ELSE /\ Q \subseteq Prev(k)
         /\ IsQuorum(Authors(Q))

-----------------------------------------------------------------------------
(* Initial state                                                           *)

Init ==
    /\ vs    = {}
    /\ es    = {}
    /\ round = [n \in N |-> 0]
    /\ log   = [n \in N |-> << >>]

-----------------------------------------------------------------------------
(* Actions                                                                 *)

(* A correct node proposes its vertex for the next round, referencing a    *)
(* quorum of previous-round vertices that includes its own previous vertex. *)
(* After GST it also includes the previous correct leader's vertex.        *)
CorrectPropose(n) ==
    /\ round[n] < MaxRound
    /\ LET k == round[n] + 1
           v == <<n, k>>
       IN  /\ v \notin vs
           /\ \E Q \in SUBSET Prev(k) :
                /\ ValidChildren(k, Q)
                /\ k > 1 => <<n, k - 1>> \in Q
                /\ (k > GST /\ Leader(k - 1) \in Correct)
                       => LeaderVertex(k - 1) \in Q
                /\ LET newEs == es \cup {<<v, q>> : q \in Q}
                   IN  /\ vs'    = vs \cup {v}
                       /\ es'    = newEs
                       /\ round' = [round EXCEPT ![n] = k]
                       /\ log'   = [log EXCEPT ![n] = Linearize(newEs, v)]

(* A Byzantine node proposes a vertex for any round in which it has no    *)
(* vertex yet. It cannot equivocate. Its vertex is only well formed (and  *)
(* thus considered) if it references a quorum of previous-round vertices. *)
ByzPropose(b) ==
    \E k \in Rounds :
       LET v == <<b, k>>
       IN  /\ v \notin vs
           /\ \E Q \in SUBSET Prev(k) :
                /\ ValidChildren(k, Q)
                /\ vs'    = vs \cup {v}
                /\ es'    = es \cup {<<v, q>> : q \in Q}
                /\ round' = [round EXCEPT ![b] = IF k > @ THEN k ELSE @]
                /\ UNCHANGED log

(* Once all correct nodes have finished the bounded run, the system stutters. *)
Done ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Correct : CorrectPropose(n)
    \/ \E b \in Byz : ByzPropose(b)
    \/ Done

Spec == Init /\ [][Next]_vars /\ \A n \in Correct : WF_vars(CorrectPropose(n))

-----------------------------------------------------------------------------
(* Invariants                                                              *)

DAGValid ==
    /\ \A v \in vs : v[1] \in N /\ v[2] \in Rounds
    /\ \A e \in es : e[1] \in vs /\ e[2] \in vs
    /\ \A e \in es : e[2][2] = e[1][2] - 1
    /\ \A v \in vs : v[2] > 1 => IsQuorum(Authors(ChildrenIn(es, v)))
    /\ \A v \in vs : v[2] = 1 => ChildrenIn(es, v) = {}

TypeOK ==
    /\ vs \subseteq Vertex
    /\ es \subseteq (Vertex \X Vertex)
    /\ round \in [N -> 0..MaxRound]
    /\ log \in [N -> Seq(Vertex)]
    /\ DAGValid

Compatible(s, t) ==
    LET m == IF Len(s) <= Len(t) THEN Len(s) ELSE Len(t)
    IN  \A i \in 1..m : s[i] = t[i]

\* Safety: logs of correct nodes never conflict
Agreement ==
    \A n1, n2 \in Correct : Compatible(log[n1], log[n2])

\* Logs of correct nodes only grow (a produced prefix is never retracted)
LogMonotone ==
    [][\A n \in Correct : Compatible(log[n], log'[n]) /\ Len(log'[n]) >= Len(log[n])]_vars

-----------------------------------------------------------------------------
(* Liveness under partial synchrony: after GST, if the leader of round r  *)
(* is correct, every correct node that is at least two rounds ahead        *)
(* eventually has the leader's vertex in its causal history.               *)

Liveness ==
    \A r \in Rounds, n \in Correct :
        (/\ r >= GST
         /\ Leader(r) \in Correct
         /\ round[n] >= r + 2)
        ~> (LeaderVertex(r) \in HistE(es, <<n, round[n]>>))

=============================================================================