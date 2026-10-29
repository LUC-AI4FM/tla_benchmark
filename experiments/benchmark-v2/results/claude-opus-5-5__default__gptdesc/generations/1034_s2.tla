------------------------------ MODULE SailfishBounded ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxRound   \* upper bound on explored rounds for correct nodes

ASSUME MaxRound \in Nat /\ MaxRound >= 1

-----------------------------------------------------------------------------
(* Concrete bounded configuration: three nodes, one Byzantine              *)
-----------------------------------------------------------------------------
N == {"n1", "n2", "n3"}
B == {"n3"}              \* Byzantine nodes
P == N \ B               \* correct (non-faulty) nodes

F == Cardinality(B)

\* Quorum and blocking-set predicates
IsQuorum(Q)    == Q \subseteq N /\ Cardinality(Q) >= Cardinality(N) - F
IsBlocking(S)  == S \subseteq N /\ Cardinality(S) >= F + 1

\* Leader schedule (round-robin)
LeaderSeq == <<"n1", "n2", "n3">>
Leader(r) == LeaderSeq[(r % Len(LeaderSeq)) + 1]

\* Global stabilization time (expressed as a round number)
GST == 2

Rounds == 0..MaxRound

-----------------------------------------------------------------------------
VARIABLES
    round,          \* round[n]: last round in which correct node n created a vertex (-1 initially)
    dag,            \* set of vertices [src, rnd, edges]; at most one vertex per (src, rnd) (reliable broadcast)
    noVote,         \* noVote[r]: set of nodes that sent a no-vote for the leader of round r
    log,            \* log[n]: sequence of committed leader rounds at correct node n
    lastCommitted   \* lastCommitted[n]: highest committed leader round at n (-1 initially)

vars == <<round, dag, noVote, log, lastCommitted>>

-----------------------------------------------------------------------------
(* Helper operators                                                         *)
-----------------------------------------------------------------------------
HasVertex(s, r) == \E v \in dag : v.src = s /\ v.rnd = r

Vertex(s, r) == CHOOSE v \in dag : v.src = s /\ v.rnd = r

SourcesAt(r) == {v.src : v \in {w \in dag : w.rnd = r}}

LeaderVertexExists(r) == HasVertex(Leader(r), r)

\* nodes whose round r+1 vertex references the leader vertex of round r
Votes(r) == {v.src : v \in {w \in dag : w.rnd = r + 1 /\ Leader(r) \in w.edges}}

RECURSIVE Reach(_, _, _, _)
Reach(s, r, s2, r2) ==
    IF r < r2 THEN FALSE
    ELSE IF r = r2 THEN s = s2
    ELSE \E e \in Vertex(s, r).edges : Reach(e, r - 1, s2, r2)

\* Leaders to commit (in order) when committing the leader of round cur,
\* walking back from round rr down to (but excluding) round last.
RECURSIVE ToCommit(_, _, _)
ToCommit(cur, rr, last) ==
    IF rr <= last THEN <<>>
    ELSE IF LeaderVertexExists(rr) /\ Reach(Leader(cur), cur, Leader(rr), rr)
         THEN ToCommit(rr, rr - 1, last) \o <<rr>>
         ELSE ToCommit(cur, rr - 1, last)

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
TypeOK ==
    /\ round \in [P -> Int]
    /\ \A v \in dag : v.src \in N /\ v.rnd \in Int /\ v.edges \subseteq N
    /\ noVote \in [Rounds -> SUBSET N]
    /\ log \in [P -> Seq(Int)]
    /\ lastCommitted \in [P -> Int]

Init ==
    /\ round = [n \in P |-> -1]
    /\ dag = {}
    /\ noVote = [r \in Rounds |-> {}]
    /\ log = [n \in P |-> <<>>]
    /\ lastCommitted = [n \in P |-> -1]

-----------------------------------------------------------------------------
(* Correct node actions                                                     *)
-----------------------------------------------------------------------------

\* Correct node n creates its vertex for the next round.
AddVertex(n) ==
    LET r == round[n] + 1 IN
    /\ r <= MaxRound
    /\ ~HasVertex(n, r)
    /\ \E E \in SUBSET SourcesAt(r - 1) :
         /\ IF r = 0 THEN E = {} ELSE IsQuorum(E)
         /\ r > 0 =>
              \* a non-leader either votes for the previous leader or has no-voted
              /\ (Leader(r - 1) \notin E) => (n \in noVote[r - 1])
              \* the leader needs the previous leader or a no-vote certificate
              /\ (n = Leader(r) /\ Leader(r - 1) \notin E) => IsQuorum(noVote[r - 1])
         /\ dag' = dag \cup {[src |-> n, rnd |-> r, edges |-> E]}
         /\ round' = [round EXCEPT ![n] = r]
    /\ UNCHANGED <<noVote, log, lastCommitted>>

\* Correct node n times out on the leader of its current round and sends a no-vote.
\* After GST, correct nodes never time out on correct leaders.
Timeout(n) ==
    LET r == round[n] IN
    /\ r \in Rounds
    /\ n \notin noVote[r]
    /\ ~LeaderVertexExists(r)
    /\ (r < GST \/ Leader(r) \in B)
    /\ noVote' = [noVote EXCEPT ![r] = @ \cup {n}]
    /\ UNCHANGED <<round, dag, log, lastCommitted>>

\* Correct node n directly commits the leader of round r (and indirectly earlier leaders).
Commit(n) ==
    \E r \in Rounds :
      /\ r > lastCommitted[n]
      /\ LeaderVertexExists(r)
      /\ IsQuorum(Votes(r))
      /\ log' = [log EXCEPT ![n] = @ \o ToCommit(r, r - 1, lastCommitted[n]) \o <<r>>]
      /\ lastCommitted' = [lastCommitted EXCEPT ![n] = r]
      /\ UNCHANGED <<round, dag, noVote>>

CorrectStep(n) == AddVertex(n) \/ Timeout(n) \/ Commit(n)

-----------------------------------------------------------------------------
(* Byzantine actions                                                        *)
-----------------------------------------------------------------------------

ByzAddVertex(b) ==
    \E r \in Rounds :
      /\ ~HasVertex(b, r)
      /\ \E E \in SUBSET SourcesAt(r - 1) :
           /\ IF r = 0 THEN E = {} ELSE IsQuorum(E)
           /\ dag' = dag \cup {[src |-> b, rnd |-> r, edges |-> E]}
      /\ UNCHANGED <<round, noVote, log, lastCommitted>>

ByzNoVote(b) ==
    \E r \in Rounds :
      /\ b \notin noVote[r]
      /\ noVote' = [noVote EXCEPT ![r] = @ \cup {b}]
      /\ UNCHANGED <<round, dag, log, lastCommitted>>

ByzStep(b) == ByzAddVertex(b) \/ ByzNoVote(b)

-----------------------------------------------------------------------------
Next ==
    \/ \E n \in P : CorrectStep(n)
    \/ \E b \in B : ByzStep(b)

Fairness == \A n \in P : WF_vars(CorrectStep(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Terminating variant                                                      *)
-----------------------------------------------------------------------------
AllCorrectDone == \A n \in P : round[n] >= MaxRound

Terminating == AllCorrectDone /\ UNCHANGED vars

TerminatingSpec == Init /\ [][Next \/ Terminating]_vars /\ Fairness

-----------------------------------------------------------------------------
(* State constraint bounding rounds of non-faulty nodes                     *)
-----------------------------------------------------------------------------
StateConstraint == \A n \in P : round[n] <= MaxRound

-----------------------------------------------------------------------------
(* Safety invariants                                                        *)
-----------------------------------------------------------------------------
LogConsistency ==
    \A n1, n2 \in P : IsPrefix(log[n1], log[n2]) \/ IsPrefix(log[n2], log[n1])

UniqueVertices ==
    \A v, w \in dag : (v.src = w.src /\ v.rnd = w.rnd) => v = w

LogIncreasing ==
    \A n \in P : \A i, j \in 1..Len(log[n]) : i < j => log[n][i] < log[n][j]

-----------------------------------------------------------------------------
(* Liveness properties                                                      *)
-----------------------------------------------------------------------------
EventuallyAllDone == <>AllCorrectDone

EventuallySomeCommit == <>(\E n \in P : Len(log[n]) > 0)

-----------------------------------------------------------------------------
(* Deliberately false predicates used to obtain interesting counterexamples *)
-----------------------------------------------------------------------------
\* Violated as soon as all correct nodes finish
NotAllCorrectDone == ~AllCorrectDone
NeverAllCorrectDone == []~AllCorrectDone

\* Violated as soon as some correct node commits something
NoCommittedEntries == \A n \in P : Len(log[n]) = 0

\* Violated when some correct node has at least two committed entries
LogStaysShort == \A n \in P : Len(log[n]) < 2

\* Violated when all correct nodes finish having committed something
NotDoneWithCommit == ~(AllCorrectDone /\ \A n \in P : Len(log[n]) > 0)

\* Violated when a Byzantine leader's vertex gets committed
NoByzLeaderCommitted == \A n \in P : \A i \in 1..Len(log[n]) : Leader(log[n][i]) \notin B

=============================================================================