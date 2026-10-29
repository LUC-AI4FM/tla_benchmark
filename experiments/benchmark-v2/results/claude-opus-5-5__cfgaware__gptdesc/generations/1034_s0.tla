---------------------------- MODULE SailfishMC ----------------------------
(***************************************************************************)
(* A small bounded configuration of the Sailfish DAG-based BFT protocol.  *)
(* There are three nodes n1, n2, n3, and n3 is Byzantine.                  *)
(*                                                                         *)
(* Vertices are reliably broadcast, so each node has at most one vertex    *)
(* per round. A vertex records its set of strong edges, which point to     *)
(* the sources of round r-1 vertices.                                      *)
(*                                                                         *)
(* A correct node moves to round r+1 once it holds a quorum of round r     *)
(* vertices. After GST it must also include the round r leader's vertex,   *)
(* unless that leader is faulty (the timeout case).                        *)
(*                                                                         *)
(* A leader vertex is committed directly when a quorum of next-round       *)
(* vertices references it. Earlier uncommitted leader vertices that the    *)
(* committed leader can reach are ordered indirectly before it.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS n1, n2, n3

N == {n1, n2, n3}          \* all nodes
Byz == {n3}                \* Byzantine nodes
C == N \ Byz               \* correct nodes

IsQuorum(Q) == Q \subseteq N /\ Cardinality(Q) >= 2
IsBlocking(B) == B \subseteq N /\ Cardinality(B) >= 1

GST == 2
MaxRound == 3
Rounds == 0..MaxRound

Leader(r) == CASE r % 3 = 0 -> n1
               [] r % 3 = 1 -> n2
               [] OTHER     -> n3

VARIABLES dag, round, log
vars == <<dag, round, log>>

VertexType == [present : BOOLEAN, edges : SUBSET N]
NoVertex == [present |-> FALSE, edges |-> {}]

Present(r) == {s \in N : dag[r][s].present}

\* Ancestors of the vertex of node s at round r (inclusive), as <<s, r>> pairs
RECURSIVE Ancestors(_, _)
Ancestors(s, r) ==
    {<<s, r>>} \cup
      (IF r = 0 THEN {}
       ELSE UNION {Ancestors(t, r - 1) : t \in dag[r][s].edges})

LastRound(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])]

-----------------------------------------------------------------------------
Init ==
    /\ dag = [r \in Rounds |-> [s \in N |->
                IF r = 0 THEN [present |-> TRUE, edges |-> {}] ELSE NoVertex]]
    /\ round = [n \in C |-> 0]
    /\ log = [n \in C |-> <<>>]

\* A correct node creates its vertex for the next round
CorrectAdvance(n) ==
    LET r == round[n] IN
    /\ r < MaxRound
    /\ \E E \in SUBSET Present(r) :
          /\ IsQuorum(E)
          /\ \/ r = 0
             \/ r < GST
             \/ Leader(r) \in Byz
             \/ Leader(r) \in E
          /\ dag' = [dag EXCEPT ![r + 1][n] = [present |-> TRUE, edges |-> E]]
    /\ round' = [round EXCEPT ![n] = r + 1]
    /\ UNCHANGED log

\* A Byzantine node may create a vertex in any round, with arbitrary edges.
\* Reliable broadcast prevents it from equivocating.
ByzCreate(b) ==
    \E r \in 1..MaxRound :
        /\ ~dag[r][b].present
        /\ \E E \in SUBSET Present(r - 1) :
              dag' = [dag EXCEPT ![r][b] = [present |-> TRUE, edges |-> E]]
        /\ UNCHANGED <<round, log>>

Votes(r) == {s \in Present(r + 1) : Leader(r) \in dag[r + 1][s].edges}

CanCommit(n, r) ==
    /\ r \in 1..(MaxRound - 1)
    /\ r > LastRound(n)
    /\ round[n] >= r + 1
    /\ dag[r][Leader(r)].present
    /\ IsQuorum(Votes(r))

\* Commit the leader of round r, plus earlier leaders it can reach
Commit(n) ==
    \E r \in 1..(MaxRound - 1) :
        /\ CanCommit(n, r)
        /\ LET anc == Ancestors(Leader(r), r)
               prev == {q \in (LastRound(n) + 1)..(r - 1) :
                           /\ dag[q][Leader(q)].present
                           /\ <<Leader(q), q>> \in anc}
               RECURSIVE ToSeq(_)
               ToSeq(S) == IF S = {} THEN <<>>
                           ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y
                                IN <<m>> \o ToSeq(S \ {m})
           IN log' = [log EXCEPT ![n] = log[n] \o ToSeq(prev) \o <<r>>]
        /\ UNCHANGED <<dag, round>>

Next ==
    \/ \E n \in C : CorrectAdvance(n)
    \/ \E n \in C : Commit(n)
    \/ \E b \in Byz : ByzCreate(b)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in C : CorrectAdvance(n) \/ Commit(n))

-----------------------------------------------------------------------------
\* Terminating variant: once every correct node has finished, the system stutters
AllCorrectDone ==
    /\ \A n \in C : round[n] = MaxRound
    /\ \A n \in C : \A r \in 1..(MaxRound - 1) : ~CanCommit(n, r)

Terminating == AllCorrectDone /\ UNCHANGED vars

TerminatingSpec ==
    Init /\ [][Next \/ Terminating]_vars
         /\ WF_vars((\E n \in C : CorrectAdvance(n)) \/ (\E n \in C : Commit(n)))

-----------------------------------------------------------------------------
TypeOK ==
    /\ dag \in [Rounds -> [N -> VertexType]]
    /\ round \in [C -> Rounds]
    /\ log \in [C -> Seq(1..MaxRound)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A a, b \in C : IsPrefix(log[a], log[b]) \/ IsPrefix(log[b], log[a])

Liveness == <>(\A n \in C : Len(log[n]) > 0)

StateConstraint == \A n \in C : round[n] <= MaxRound

\* Deliberately false predicates, used to make TLC produce interesting traces
NotAllCorrectFinished == ~AllCorrectDone
NoCommitEver == \A n \in C : log[n] = <<>>
NeverTwoCommits == \A n \in C : Len(log[n]) < 2
NeverAllFinishTemporal == [](~AllCorrectDone)
=============================================================================