------------------------------- MODULE SailfishBounded -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS n1, n2, n3

ASSUME n1 # n2 /\ n2 # n3 /\ n1 # n3

N == {n1, n2, n3}          \* all nodes
F == {n3}                  \* Byzantine nodes
P == N \ F                 \* correct nodes

IsQuorum(Q)   == Q \subseteq N /\ Cardinality(Q) >= 2
IsBlocking(B) == B \subseteq N /\ Cardinality(B) >= 1

Leader(r) == CASE r % 3 = 1 -> n1
               [] r % 3 = 2 -> n2
               [] OTHER     -> n3

GST      == 2              \* round from which the network is synchronous
MaxRound == 4              \* bound on explored rounds

Vertices == [node : N, round : 1..MaxRound, edges : SUBSET N]

VARIABLES dag, delivered, round, log

vars == <<dag, delivered, round, log>>

TypeOK ==
    /\ dag \subseteq Vertices
    /\ delivered \in [P -> SUBSET Vertices]
    /\ round \in [P -> 1..(MaxRound + 1)]
    /\ log \in [P -> Seq(1..MaxRound)]

IsLeaderVertex(v) == v.node = Leader(v.round)

RECURSIVE Reaches(_, _, _)
Reaches(v, w, D) ==
    IF v.round = w.round THEN v = w
    ELSE IF v.round < w.round THEN FALSE
    ELSE \E u \in D : /\ u.round = v.round - 1
                      /\ u.node \in v.edges
                      /\ Reaches(u, w, D)

LastCommitted(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])]

RECURSIVE CommitChain(_, _, _)
CommitChain(l, lastR, D) ==
    LET C == { lv \in D : /\ IsLeaderVertex(lv)
                          /\ lastR < lv.round
                          /\ lv.round < l.round
                          /\ Reaches(l, lv, D) }
    IN IF C = {} THEN <<l.round>>
       ELSE LET m == CHOOSE c \in C : \A c2 \in C : c2.round <= c.round
            IN CommitChain(m, lastR, D) \o <<l.round>>

Init ==
    /\ dag = {}
    /\ delivered = [n \in P |-> {}]
    /\ round = [n \in P |-> 1]
    /\ log = [n \in P |-> <<>>]

\* A correct node broadcasts its vertex for its current round.
Broadcast(n) ==
    LET r    == round[n]
        prev == {v \in delivered[n] : v.round = r - 1}
    IN /\ r <= MaxRound
       /\ r = 1 \/ IsQuorum({v.node : v \in prev})
       \* After GST, wait for the vertex of a correct leader (no premature timeout)
       /\ (r > 1 /\ r - 1 >= GST /\ Leader(r - 1) \in P)
              => \E v \in prev : v.node = Leader(r - 1)
       /\ LET v == [node |-> n, round |-> r, edges |-> {u.node : u \in prev}]
          IN /\ dag' = dag \cup {v}
             /\ delivered' = [delivered EXCEPT ![n] = @ \cup {v}]
       /\ round' = [round EXCEPT ![n] = r + 1]
       /\ UNCHANGED log

\* A Byzantine node broadcasts an arbitrary (but RBC-valid) vertex.
ByzBroadcast(b, r, E) ==
    /\ ~\E v \in dag : v.node = b /\ v.round = r
    /\ E \subseteq {v.node : v \in {w \in dag : w.round = r - 1}}
    /\ r = 1 => E = {}
    /\ r > 1 => IsQuorum(E)
    /\ dag' = dag \cup {[node |-> b, round |-> r, edges |-> E]}
    /\ UNCHANGED <<delivered, round, log>>

\* Reliable-broadcast delivery respecting causality.
Deliver(n, v) ==
    /\ v \in dag \ delivered[n]
    /\ \A m \in v.edges : \E u \in delivered[n] : u.node = m /\ u.round = v.round - 1
    /\ delivered' = [delivered EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<dag, round, log>>

\* Direct commit of a leader vertex supported by a quorum of next-round vertices.
Commit(n) ==
    \E l \in delivered[n] :
        /\ IsLeaderVertex(l)
        /\ l.round > LastCommitted(n)
        /\ IsQuorum({w.node : w \in {x \in delivered[n] :
                                        x.round = l.round + 1 /\ l.node \in x.edges}})
        /\ log' = [log EXCEPT ![n] = @ \o CommitChain(l, LastCommitted(n), delivered[n])]
        /\ UNCHANGED <<dag, delivered, round>>

CorrectStep(n) ==
    \/ Broadcast(n)
    \/ \E v \in dag : Deliver(n, v)
    \/ Commit(n)

ByzStep ==
    \E b \in F, r \in 1..MaxRound, E \in SUBSET N : ByzBroadcast(b, r, E)

Next ==
    \/ \E n \in P : CorrectStep(n)
    \/ ByzStep

Fairness ==
    \A n \in P :
        /\ WF_vars(Broadcast(n))
        /\ WF_vars(\E v \in dag : Deliver(n, v))
        /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Terminating variant: once all correct nodes have finished, stutter.
Finished(n) == round[n] > MaxRound
AllCorrectFinished == \A n \in P : Finished(n)

Terminating == AllCorrectFinished /\ UNCHANGED vars

TerminatingNext == Next \/ Terminating

TerminatingSpec == Init /\ [][TerminatingNext]_vars /\ Fairness

\* State constraint bounding explored rounds of non-faulty nodes.
StateConstraint == \A n \in P : round[n] <= MaxRound + 1

\* Safety
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Consistency ==
    \A n, m \in P : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

LogIncreasing ==
    \A n \in P : \A i, j \in 1..Len(log[n]) : i < j => log[n][i] < log[n][j]

Safety == TypeOK /\ Consistency /\ LogIncreasing

\* Liveness
Termination == <>AllCorrectFinished

EventuallyCommit == <>(\A n \in P : Len(log[n]) > 0)

\* Deliberately false predicates, to make TLC produce interesting executions
Falsy_NeverAllFinish == [](~AllCorrectFinished)
Falsy_NoCommit == \A n \in P : log[n] = <<>>
Falsy_ShortLog == \A n \in P : Len(log[n]) < 2
Falsy_NotFinishedWithCommits ==
    ~(AllCorrectFinished /\ \A n \in P : Len(log[n]) > 0)
Falsy_NeverCommitAll == [](~(\A n \in P : Len(log[n]) > 0))

=====================================================================================