---------------------------- MODULE TLCSailfish1 ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS n1, n2, n3

VARIABLES vs, es, round, log

vars == <<vs, es, round, log>>

(***************************************************************************)
(* Scenario parameters                                                     *)
(***************************************************************************)
P == {n1, n2, n3}
F == {n1}
Correct == P \ F
R == 1..5
MaxRound == 5
GST == 3

Quorum == {Q \in SUBSET P : n3 \in Q /\ Cardinality(Q) >= 2} \cup {P}
Blocking == {B \in SUBSET P : n3 \in B}

Leader(r) == CASE r % 3 = 1 -> n1
               [] r % 3 = 2 -> n2
               [] OTHER     -> n3

LeaderVertex(r) == <<Leader(r), r>>

Vertices == P \X R

(***************************************************************************)
(* DAG helpers                                                             *)
(***************************************************************************)
Votes(l) == {v \in vs : v[2] = l[2] + 1 /\ <<v, l>> \in es}
VoteNodes(l) == {v[1] : v \in Votes(l)}

Blocked(l) == \E B \in Blocking : B \subseteq VoteNodes(l)

Committable(l) == l \in vs /\ \E Q \in Quorum : Q \subseteq VoteNodes(l)

RECURSIVE Reach(_)
Reach(v) == {v} \cup UNION {Reach(e[2]) : e \in {f \in es : f[1] = v}}

RECURSIVE Chain(_)
Chain(l) ==
    LET cands == {w \in Reach(l) : /\ w # l
                                   /\ w = LeaderVertex(w[2])
                                   /\ Blocked(w)}
    IN IF cands = {}
         THEN <<l>>
         ELSE LET p == CHOOSE w \in cands : \A u \in cands : u[2] <= w[2]
              IN Append(Chain(p), l)

\* Possible parent sets for a vertex of round r: a quorum of round r-1 vertices
Parents(r) ==
    IF r = 1
      THEN {{}}
      ELSE {{<<m, r - 1>> : m \in S} :
              S \in {S \in Quorum : \A m \in S : <<m, r - 1>> \in vs}}

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Init ==
    /\ vs = {}
    /\ es = {}
    /\ round = [n \in P |-> 0]
    /\ log = [n \in P |-> <<>>]

CorrectAdd(n) ==
    /\ n \in Correct
    /\ LET r == round[n] + 1 IN
         /\ r \in R
         /\ <<n, r>> \notin vs
         /\ \E Ps \in Parents(r) :
              /\ (r > 1 /\ r - 1 >= GST /\ Leader(r - 1) \notin F)
                    => LeaderVertex(r - 1) \in Ps
              /\ vs' = vs \cup {<<n, r>>}
              /\ es' = es \cup {<<<<n, r>>, p>> : p \in Ps}
              /\ round' = [round EXCEPT ![n] = r]
    /\ UNCHANGED log

ByzAdd(n) ==
    /\ n \in F
    /\ \E r \in R :
         /\ <<n, r>> \notin vs
         /\ \E Ps \in Parents(r) :
              /\ vs' = vs \cup {<<n, r>>}
              /\ es' = es \cup {<<<<n, r>>, p>> : p \in Ps}
              /\ round' = [round EXCEPT ![n] = IF r > @ THEN r ELSE @]
    /\ UNCHANGED log

Commit(n) ==
    /\ n \in Correct
    /\ \E r \in R :
         LET l == LeaderVertex(r) IN
           /\ l \in vs
           /\ round[n] > r
           /\ Committable(l)
           /\ \/ log[n] = <<>>
              \/ log[n][Len(log[n])][2] < r
           /\ log' = [log EXCEPT ![n] = Chain(l)]
    /\ UNCHANGED <<vs, es, round>>

Next == \E n \in P : CorrectAdd(n) \/ ByzAdd(n) \/ Commit(n)

Spec == Init /\ [][Next]_vars

Done == \A n \in Correct : round[n] = MaxRound

TerminatingSpec == Init /\ [][Next \/ (Done /\ UNCHANGED vars)]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ vs \subseteq Vertices
    /\ es \subseteq Vertices \X Vertices
    /\ round \in [P -> 0..MaxRound]
    /\ \A n \in P : /\ log[n] \in Seq(Vertices)
                    /\ Len(log[n]) <= MaxRound

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A a, b \in Correct : IsPrefix(log[a], log[b]) \/ IsPrefix(log[b], log[a])

Liveness ==
    Done => \E r \in GST..(MaxRound - 1) :
              /\ Leader(r) \notin F
              /\ Committable(LeaderVertex(r))

StateConstraint == \A n \in Correct : round[n] <= MaxRound

(***************************************************************************)
(* Falsy properties: used as false invariants to obtain example traces    *)
(***************************************************************************)
Falsy1 == ~Done
Falsy2 == \A n \in Correct : Len(log[n]) <= 1
Falsy3 == ~(\E n \in Correct : \E i \in DOMAIN log[n] : log[n][i] = LeaderVertex(2))

=============================================================================