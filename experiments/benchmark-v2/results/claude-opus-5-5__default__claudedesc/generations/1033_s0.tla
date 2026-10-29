------------------------------ MODULE Sailfish ------------------------------
(***************************************************************************)
(* Sailfish: a DAG-based Byzantine fault-tolerant consensus protocol.      *)
(* This specification abstracts over the differences between Sailfish and *)
(* its signature-free variant.                                            *)
(*                                                                         *)
(* A vertex is a pair <<node, round>>. Because a vertex is identified by  *)
(* its creator and its round, no node, Byzantine or not, can equivocate.  *)
(* An edge <<v, w>> means that vertex v references vertex w.              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,              \* the set of all nodes
    F,              \* the set of Byzantine nodes
    R,              \* the set of rounds, e.g. 1..MaxRound
    IsQuorum(_),    \* quorum predicate on sets of nodes
    IsBlocking(_),  \* blocking-set predicate on sets of nodes
    Leader(_),      \* maps a round to its leader node
    GST             \* round from which the network is synchronous

ASSUME F \subseteq N
ASSUME R \subseteq Nat \ {0}
ASSUME \A r \in R : Leader(r) \in N
ASSUME GST \in Nat

VARIABLES
    vs,     \* the set of DAG vertices
    es,     \* the set of DAG edges
    round,  \* round[n]: the current round of correct node n
    log     \* log[n]: the committed log of correct node n

vars == <<vs, es, round, log>>

Correct == N \ F

Genesis == <<"Genesis", 0>>

Vertex == (N \X R) \cup {Genesis}

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
Sources(S) == {u[1] : u \in S}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

IsLeaderV(v) == v # Genesis /\ v[1] = Leader(v[2])

LogSet(lg) == {lg[i] : i \in DOMAIN lg}

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

\* Causal history of v in the current DAG, including v itself
RECURSIVE Reach(_)
Reach(v) == {v} \cup UNION {Reach(e[2]) : e \in {x \in es : x[1] = v}}

\* Deterministic linearization of a set of vertices, ordered by round
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN << >>
    ELSE LET m == CHOOSE x \in S : \A y \in S : x[2] <= y[2]
         IN  <<m>> \o SetToSeq(S \ {m})

\* Round of the highest leader vertex already in a log (0 if there is none)
LastLeaderRound(lg) ==
    LET L == {v[2] : v \in {x \in LogSet(lg) : IsLeaderV(x)}}
    IN  IF L = {} THEN 0 ELSE Max(L)

\* Leaders to commit, in order, when leader l is committed directly
RECURSIVE LeaderChain(_, _)
LeaderChain(l, lr) ==
    LET prev == {v \in Reach(l) : v # l /\ IsLeaderV(v) /\ v[2] > lr}
    IN  IF prev = {} THEN <<l>>
        ELSE LeaderChain(CHOOSE p \in prev : \A q \in prev : q[2] <= p[2], lr)
                \o <<l>>

\* Append the not-yet-committed causal history of each leader in chain
RECURSIVE AppendAll(_, _)
AppendAll(lg, chain) ==
    IF chain = << >> THEN lg
    ELSE LET done == LogSet(lg)
             new  == SetToSeq(Reach(Head(chain)) \ (done \cup {Genesis}))
         IN  AppendAll(lg \o new, Tail(chain))

(***************************************************************************)
(* Leader rule for entering round r with the set S of observed            *)
(* round r-1 vertices. If the leader vertex of round r-1 is observed,     *)
(* then either it references the leader vertex of round r-2, or there is  *)
(* quorum evidence (a quorum of round r-1 vertices not referencing the    *)
(* leader of round r-2) that the round r-2 leader cannot commit.          *)
(***************************************************************************)
LeaderRule(S, r) ==
    IF (r - 1) \in R /\ (r - 2) \in R
    THEN LET pl  == <<Leader(r - 1), r - 1>>
             ppl == <<Leader(r - 2), r - 2>>
         IN  pl \in S =>
                \/ <<pl, ppl>> \in es
                \/ \E Q \in SUBSET S :
                      /\ IsQuorum(Sources(Q))
                      /\ \A u \in Q : <<u, ppl>> \notin es
    ELSE TRUE

\* The new log of node n after it enters round r having observed S
NewLog(n, S, r) ==
    IF (r - 2) \in R
    THEN LET lv    == <<Leader(r - 2), r - 2>>
             votes == {u \in S : <<u, lv>> \in es}
         IN  IF /\ lv \in vs
                /\ IsQuorum(Sources(votes))
                /\ lv \notin LogSet(log[n])
             THEN AppendAll(log[n], LeaderChain(lv, LastLeaderRound(log[n])))
             ELSE log[n]
    ELSE log[n]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ vs = {Genesis}
    /\ es = {}
    /\ round = [n \in Correct |-> 0]
    /\ log = [n \in Correct |-> << >>]

(***************************************************************************)
(* Correct node actions                                                    *)
(***************************************************************************)

\* A correct node creates its round-1 vertex, which references Genesis.
Start(n) ==
    /\ round[n] = 0
    /\ 1 \in R
    /\ <<n, 1>> \notin vs
    /\ vs' = vs \cup {<<n, 1>>}
    /\ es' = es \cup {<<<<n, 1>>, Genesis>>}
    /\ round' = [round EXCEPT ![n] = 1]
    /\ UNCHANGED log

\* A correct node advances from round r-1 to round r.
Advance(n) ==
    /\ round[n] >= 1
    /\ \E r \in R :
        /\ r = round[n] + 1
        /\ <<n, r>> \notin vs
        /\ \E S \in SUBSET {v \in vs : v # Genesis /\ v[2] = r - 1} :
            /\ IsQuorum(Sources(S))
            \* after GST, all correct nodes' vertices must be observed
            /\ (r - 1 >= GST) => (\A m \in Correct : <<m, r - 1>> \in S)
            /\ LeaderRule(S, r)
            /\ vs' = vs \cup {<<n, r>>}
            /\ es' = es \cup {<<<<n, r>>, u>> : u \in S}
            /\ round' = [round EXCEPT ![n] = r]
            /\ log' = [log EXCEPT ![n] = NewLog(n, S, r)]

(***************************************************************************)
(* Byzantine node actions: they may create vertices in any round, but     *)
(* they cannot equivocate and must reference a quorum of vertices from    *)
(* the previous round.                                                     *)
(***************************************************************************)
ByzantineCreate(b) ==
    \E r \in R :
        /\ <<b, r>> \notin vs
        /\ IF r = 1
           THEN /\ vs' = vs \cup {<<b, 1>>}
                /\ es' = es \cup {<<<<b, 1>>, Genesis>>}
           ELSE \E S \in SUBSET {v \in vs : v # Genesis /\ v[2] = r - 1} :
                   /\ IsQuorum(Sources(S))
                   /\ vs' = vs \cup {<<b, r>>}
                   /\ es' = es \cup {<<<<b, r>>, u>> : u \in S}
        /\ UNCHANGED <<round, log>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
Next ==
    \/ \E n \in Correct : Start(n) \/ Advance(n)
    \/ \E b \in F : ByzantineCreate(b)

Fairness ==
    \A n \in Correct : WF_vars(Start(n) \/ Advance(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ vs \subseteq Vertex
    /\ es \subseteq Vertex \X Vertex
    /\ round \in [Correct -> R \cup {0}]
    /\ log \in [Correct -> Seq(Vertex)]

\* The logs of correct nodes are prefix-compatible.
Agreement ==
    \A n1, n2 \in Correct :
        IsPrefix(log[n1], log[n2]) \/ IsPrefix(log[n2], log[n1])

\* After GST, a correct leader's vertex eventually appears in the log of
\* every correct node. This applies to leaders whose round is far enough
\* from the last round for a quorum of votes to be collected.
Liveness ==
    \A r \in R :
        (/\ r >= GST
         /\ Leader(r) \in Correct
         /\ (r + 2) \in R)
        => <>(\A n \in Correct : <<Leader(r), r>> \in LogSet(log[n]))

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => Liveness
=============================================================================