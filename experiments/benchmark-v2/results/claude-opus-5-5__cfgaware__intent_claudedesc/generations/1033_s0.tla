---------------------------- MODULE DAGConsensus ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

VARIABLES vs, es, round, log

vars == <<vs, es, round, log>>

Nodes == 1..N
F == (N - 1) \div 3
Correct == 1..(N - F)
Byzantine == Nodes \ Correct

MaxRound == 4
GST == 2
Rounds == 1..MaxRound

Quorum(S) == Cardinality(S) >= N - F
Blocking(S) == Cardinality(S) >= F + 1

Leader(r) == ((r - 1) % N) + 1

Genesis == <<0, 0>>
Vertices == {Genesis} \cup (Nodes \X Rounds)

LB(r) == <<Leader(r), r>>

RoundBlocks(r) == {v \in vs : v[2] = r}

NodesOf(S) == {v[1] : v \in S}

RECURSIVE Hist(_)
Hist(v) == {v} \cup UNION {Hist(e[2]) : e \in {x \in es : x[1] = v}}

Less(x, y) == x[2] < y[2] \/ (x[2] = y[2] /\ x[1] < y[1])

RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN << >>
    ELSE LET m == CHOOSE x \in S : \A y \in S : x = y \/ Less(x, y)
         IN <<m>> \o SetToSeq(S \ {m})

MaxOf(C) == CHOOSE m \in C : \A x \in C : x <= m

PrevLeader(L) ==
    LET r == L[2]
        H == Hist(L)
        C == {r2 \in 1..(r - 2) :
                /\ LB(r2) \in H
                /\ Blocking(NodesOf({w \in H : w[2] = r2 + 1 /\ <<w, LB(r2)>> \in es}))}
    IN IF r <= 1 THEN Genesis
       ELSE IF <<L, LB(r - 1)>> \in es THEN LB(r - 1)
       ELSE IF C = {} THEN Genesis
       ELSE LB(MaxOf(C))

RECURSIVE Linearize(_)
Linearize(L) ==
    IF L = Genesis THEN << >>
    ELSE LET P == PrevLeader(L)
         IN Linearize(P) \o SetToSeq(Hist(L) \ Hist(P))

ValidRefs(n, r, R) ==
    /\ R \subseteq RoundBlocks(r - 1)
    /\ IF r = 1 THEN R = {Genesis} ELSE Quorum(NodesOf(R))
    /\ (n = Leader(r) /\ r >= 2) =>
          \/ LB(r - 1) \in R
          \/ Quorum(NodesOf({v \in RoundBlocks(r) : <<v, LB(r - 1)>> \notin es}
                            \cup {<<n, r>>}))

AddBlock(n, r, R) ==
    /\ vs' = vs \cup {<<n, r>>}
    /\ es' = es \cup {<<<<n, r>>, v>> : v \in R}

CorrectStep(n) ==
    LET r == round[n] + 1 IN
    /\ r <= MaxRound
    /\ \E R \in SUBSET RoundBlocks(r - 1) :
        /\ ValidRefs(n, r, R)
        /\ (r > GST) => (\A c \in Correct : <<c, r - 1>> \in R)
        /\ AddBlock(n, r, R)
        /\ round' = [round EXCEPT ![n] = r]
        /\ log' = IF r >= 3
                     /\ Quorum(NodesOf({v \in R : <<v, LB(r - 2)>> \in es}))
                  THEN [log EXCEPT ![n] = Linearize(LB(r - 2))]
                  ELSE log

ByzStep(b) ==
    \E r \in Rounds :
        /\ <<b, r>> \notin vs
        /\ \E R \in SUBSET RoundBlocks(r - 1) :
            /\ ValidRefs(b, r, R)
            /\ AddBlock(b, r, R)
            /\ round' = [round EXCEPT ![b] = IF r > @ THEN r ELSE @]
            /\ UNCHANGED log

Terminated ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

Init ==
    /\ vs = {Genesis}
    /\ es = {}
    /\ round = [n \in Nodes |-> 0]
    /\ log = [n \in Correct |-> << >>]

Next ==
    \/ \E n \in Correct : CorrectStep(n)
    \/ \E b \in Byzantine : ByzStep(b)
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ \A n \in Correct : WF_vars(CorrectStep(n))

TypeOK ==
    /\ vs \subseteq Vertices
    /\ es \subseteq (Vertices \X Vertices)
    /\ round \in [Nodes -> 0..MaxRound]
    /\ log \in [Correct -> Seq(Vertices)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

InLog(n, v) == \E i \in 1..Len(log[n]) : log[n][i] = v

Liveness ==
    \A r \in GST..(MaxRound - 2) :
        Leader(r) \in Correct =>
            \A n \in Correct : (round[n] >= r + 2) ~> InLog(n, LB(r))

=============================================================================