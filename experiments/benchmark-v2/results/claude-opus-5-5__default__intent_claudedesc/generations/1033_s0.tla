---------------------------- MODULE DAGConsensus ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,          \* set of all nodes
    C,          \* set of correct nodes
    MaxRound,   \* rounds are 1..MaxRound
    Quorum,     \* set of quorums (each a subset of N, e.g. size n-f)
    Blocking,   \* set of blocking sets (each a subset of N, e.g. size f+1)
    Leader,     \* function from 1..MaxRound to N
    GST         \* global stabilization round

ASSUME
    /\ C \subseteq N
    /\ MaxRound \in Nat \ {0}
    /\ Quorum \subseteq SUBSET N
    /\ Blocking \subseteq SUBSET N
    /\ Leader \in [1..MaxRound -> N]
    /\ GST \in Nat

Byz == N \ C
Rounds == 1..MaxRound

IsQuorum(S) == \E Q \in Quorum : Q \subseteq S
IsBlocking(S) == \E B \in Blocking : B \subseteq S

Genesis == [round |-> 0, source |-> "genesis", edges |-> {}]

VARIABLES
    vs,         \* vertices delivered by reliable broadcast (global)
    dag,        \* dag[n]: vertices received by correct node n
    round,      \* round[n]: current round of correct node n
    log,        \* log[n]: committed sequence of vertices of node n
    lastLeader  \* lastLeader[n]: round of last committed leader at n

vars == <<vs, dag, round, log, lastLeader>>

(* ---------------- Helpers ---------------- *)

RECURSIVE Reach(_)
Reach(v) == {v} \cup UNION {Reach(e) : e \in v.edges}

RECURSIVE ToSeq(_)
ToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET v == CHOOSE x \in S : \A y \in S : x.round <= y.round
         IN  <<v>> \o ToSeq(S \ {v})

Range(s) == {s[i] : i \in DOMAIN s}

AtRound(S, r) == {v \in S : v.round = r}
Sources(S) == {v.source : v \in S}

LeaderVertices(S, r) ==
    {v \in AtRound(S, r) : v.source = Leader[r]}

Votes(S, l) == {v \in AtRound(S, l.round + 1) : l \in v.edges}
NonVotes(S, l) == {v \in AtRound(S, l.round + 1) : l \notin v.edges}

\* Before the leader of round r+1 creates a block not referencing the
\* leader of round r, there must be a quorum of non-votes for that leader.
SafeLeaderBlock(n, r1, E, S) ==
    (r1 > 1 /\ n = Leader[r1]) =>
        \A l \in LeaderVertices(S, r1 - 1) :
            l \notin E => IsQuorum(Sources(NonVotes(S, l)))

IsPrefix(s, t) ==
    Len(s) <= Len(t) /\ \A i \in 1..Len(s) : s[i] = t[i]

(* ---------------- Initial state ---------------- *)

Init ==
    /\ vs = {Genesis}
    /\ dag = [n \in C |-> {Genesis}]
    /\ round = [n \in C |-> 0]
    /\ log = [n \in C |-> <<>>]
    /\ lastLeader = [n \in C |-> 0]

(* ---------------- Actions ---------------- *)

\* Correct node n receives a broadcast vertex whose causal history it has.
Receive(n) ==
    \E v \in vs \ dag[n] :
        /\ v.edges \subseteq dag[n]
        /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
        /\ UNCHANGED <<vs, round, log, lastLeader>>

\* Correct node n advances from round r to r+1 and creates its block.
Advance(n) ==
    LET r  == round[n]
        r1 == r + 1
        E  == IF r = 0 THEN {Genesis} ELSE AtRound(dag[n], r)
    IN
    /\ r < MaxRound
    /\ r > 0 => IsQuorum(Sources(E))
    /\ (r > 0 /\ r >= GST) => C \subseteq Sources(E)
    /\ SafeLeaderBlock(n, r1, E, dag[n])
    /\ LET v == [round |-> r1, source |-> n, edges |-> E]
       IN  /\ vs' = vs \cup {v}
           /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
    /\ round' = [round EXCEPT ![n] = r1]
    /\ UNCHANGED <<log, lastLeader>>

\* Correct node n commits the leader of round r once it sees a quorum
\* of votes for it, linearizing its causal history into the log.
Commit(n) ==
    \E r \in Rounds :
        /\ r > lastLeader[n]
        /\ round[n] >= r + 2
        /\ \E l \in LeaderVertices(dag[n], r) :
            /\ IsQuorum(Sources(Votes(dag[n], l)))
            /\ log' = [log EXCEPT ![n] =
                         @ \o ToSeq(Reach(l) \ (Range(@) \cup {Genesis}))]
            /\ lastLeader' = [lastLeader EXCEPT ![n] = r]
        /\ UNCHANGED <<vs, dag, round>>

\* Byzantine node b creates a block at any round; reliable broadcast
\* prevents equivocation and requires a valid quorum of references.
ByzCreate(b) ==
    \E r1 \in Rounds :
        /\ ~\E v \in vs : v.source = b /\ v.round = r1
        /\ \E E \in SUBSET (IF r1 = 1 THEN {Genesis} ELSE AtRound(vs, r1 - 1)) :
            /\ r1 = 1 => E = {Genesis}
            /\ r1 > 1 => IsQuorum(Sources(E))
            /\ vs' = vs \cup {[round |-> r1, source |-> b, edges |-> E]}
        /\ UNCHANGED <<dag, round, log, lastLeader>>

Next ==
    \/ \E n \in C : Receive(n) \/ Advance(n) \/ Commit(n)
    \/ \E b \in Byz : ByzCreate(b)

Fairness ==
    \A n \in C :
        /\ WF_vars(Receive(n))
        /\ WF_vars(Advance(n))
        /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------- Properties ---------------- *)

TypeOK ==
    /\ round \in [C -> 0..MaxRound]
    /\ lastLeader \in [C -> 0..MaxRound]
    /\ \A n \in C : dag[n] \subseteq vs

\* Safety: logs of correct nodes are always compatible.
Agreement ==
    \A n, m \in C : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* No equivocation is possible (reliable broadcast).
NoEquivocation ==
    \A v, w \in vs : (v.source = w.source /\ v.round = w.round) => v = w

InLog(n, r) ==
    \E i \in DOMAIN log[n] :
        log[n][i].round = r /\ log[n][i].source = Leader[r]

\* Liveness: after GST, a correct leader's block is eventually committed
\* by every correct node that reaches at least two rounds past it.
EventualCommitment ==
    \A r \in Rounds : \A n \in C :
        (r >= GST /\ Leader[r] \in C) =>
            [](round[n] >= r + 2 => <>InLog(n, r))

THEOREM Spec => [](TypeOK /\ Agreement /\ NoEquivocation)
THEOREM Spec => EventualCommitment
=============================================================================