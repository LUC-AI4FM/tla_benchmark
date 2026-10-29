------------------------------- MODULE Sailfish -------------------------------
(***************************************************************************)
(* High-level specification of the Sailfish / Sailfish++ DAG-based         *)
(* consensus algorithms.                                                   *)
(*                                                                         *)
(* Vertices are disseminated using reliable broadcast. Byzantine nodes     *)
(* therefore cannot equivocate: there is at most one vertex per            *)
(* (node, round). They can only create protocol-conforming vertices, which *)
(* must pass the same quorum checks as correct vertices. Byzantine nodes   *)
(* may skip rounds, choose parents arbitrarily within the protocol rules,  *)
(* or stay silent.                                                         *)
(*                                                                         *)
(* A vertex is a pair <<node, round>>. An edge <<v, w>> means that vertex  *)
(* v references vertex w from the previous round.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

ASSUME N \in Nat /\ N >= 1

F == (N - 1) \div 3
Nodes == 1..N
Correct == 1..(N - F)
Byzantine == Nodes \ Correct
Quorum == N - F

MaxRound == 3
GST == 2   \* rounds >= GST are synchronous

Leader(r) == ((r - 1) % N) + 1
LeaderVertex(r) == <<Leader(r), r>>

VARIABLES vs, es, round, log

vars == <<vs, es, round, log>>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
RECURSIVE Reach(_, _)
Reach(v, w) ==
    \/ v = w
    \/ \E e \in es : /\ e[1] = v
                     /\ e[2][2] >= w[2]
                     /\ Reach(e[2], w)

\* Number of round-(r+1) vertices voting for (referencing) the leader of r.
Votes(r) ==
    Cardinality({m \in Nodes : << <<m, r+1>>, LeaderVertex(r) >> \in es})

\* No-vote certificate: a quorum of round-(r+1) vertices that do not
\* reference the leader vertex of round r.
NoVoteCert(r) ==
    Cardinality({m \in Nodes :
                    /\ <<m, r+1>> \in vs
                    /\ << <<m, r+1>>, LeaderVertex(r) >> \notin es}) >= Quorum

\* Order the leaders in the causal history of v, from round lo+1 on.
RECURSIVE OrderFrom(_, _)
OrderFrom(v, lo) ==
    LET C == {w \in vs : /\ w[1] = Leader(w[2])
                         /\ lo < w[2]
                         /\ w[2] < v[2]
                         /\ Reach(v, w)}
    IN IF C = {}
       THEN <<v>>
       ELSE LET w == CHOOSE x \in C : \A y \in C : y[2] <= x[2]
            IN OrderFrom(w, lo) \o <<v>>

LastRound(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])][2]

(***************************************************************************)
(* Vertex creation rules (shared by correct and Byzantine nodes)           *)
(***************************************************************************)
CanCreate(n, r, P) ==
    /\ r \in 1..MaxRound
    /\ <<n, r>> \notin vs
    /\ IF r = 1
          THEN P = {}
          ELSE /\ Cardinality(P) >= Quorum
               /\ \A m \in P : <<m, r-1>> \in vs
    \* Sailfish leader rule: the leader vertex of round r must reference the
    \* leader vertex of round r-1 or carry a no-vote certificate.
    /\ (r > 1 /\ n = Leader(r)) =>
           (Leader(r-1) \in P \/ NoVoteCert(r-1))

AddVertex(n, r, P) ==
    /\ vs' = vs \cup {<<n, r>>}
    /\ es' = es \cup { << <<n, r>>, <<m, r-1>> >> : m \in P }
    /\ round' = [round EXCEPT ![n] = r]
    /\ UNCHANGED log

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
CorrectCreate(n) ==
    /\ n \in Correct
    /\ LET r == round[n] + 1 IN
         \E P \in SUBSET Nodes :
            /\ CanCreate(n, r, P)
            \* After GST, correct nodes wait for and vote for correct leaders.
            /\ (r - 1 >= GST /\ Leader(r-1) \in Correct) => Leader(r-1) \in P
            /\ AddVertex(n, r, P)

ByzantineCreate(n) ==
    /\ n \in Byzantine
    /\ \E r \in (round[n] + 1)..MaxRound :
         \E P \in SUBSET Nodes :
            /\ CanCreate(n, r, P)
            /\ AddVertex(n, r, P)

Commit(n) ==
    /\ n \in Correct
    /\ \E r \in (LastRound(n) + 1)..(MaxRound - 1) :
         /\ LeaderVertex(r) \in vs
         /\ Votes(r) >= Quorum
         /\ log' = [log EXCEPT ![n] = @ \o OrderFrom(LeaderVertex(r), LastRound(n))]
    /\ UNCHANGED <<vs, es, round>>

Init ==
    /\ vs = {}
    /\ es = {}
    /\ round = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<>>]

Next ==
    \/ \E n \in Correct : CorrectCreate(n) \/ Commit(n)
    \/ \E n \in Byzantine : ByzantineCreate(n)
    \/ UNCHANGED vars

Fairness ==
    \A n \in Correct : WF_vars(CorrectCreate(n)) /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ vs \subseteq (Nodes \X (1..MaxRound))
    /\ es \subseteq (vs \X vs)
    /\ round \in [Nodes -> 0..MaxRound]
    /\ log \in [Nodes -> Seq(Nodes \X (1..MaxRound))]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A n1, n2 \in Correct :
        IsPrefix(log[n1], log[n2]) \/ IsPrefix(log[n2], log[n1])

InLog(n, v) == \E i \in DOMAIN log[n] : log[n][i] = v

Liveness ==
    \A r \in GST..(MaxRound - 1) :
        Leader(r) \in Correct =>
            <>(\A n \in Correct : InLog(n, LeaderVertex(r)))

===============================================================================