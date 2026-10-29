------------------------------ MODULE SailfishBFT ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS n1, n2, n3

ASSUME n1 # n2 /\ n2 # n3 /\ n1 # n3

N        == {n1, n2, n3}
Byz      == {n3}
Correct  == N \ Byz
MaxRound == 3

\* Quorums: every quorum contains all correct nodes (n = 3, f = 1).
Quorums  == {Q \in SUBSET N : Correct \subseteq Q}

\* Blocking sets: intersect every quorum and contain a correct node.
Blocking == {S \in SUBSET N : (\A Q \in Quorums : S \cap Q # {}) /\ S \cap Correct # {}}

ASSUME \A Q1, Q2 \in Quorums : Q1 \cap Q2 \cap Correct # {}
ASSUME \A S \in Blocking : \A Q \in Quorums : S \cap Q # {}

\* Rotating leader schedule.
Leader(r) == CASE r % 3 = 1 -> n1
               [] r % 3 = 2 -> n2
               [] OTHER     -> n3

Vertex == [src : N, rnd : 0..MaxRound, edges : SUBSET N]

VARIABLES round, dag, log, gst

vars == <<round, dag, log, gst>>

-------------------------------------------------------------------------------
SrcsAt(r) == {v.src : v \in {w \in dag : w.rnd = r}}

HasVertex(s, r) == \E v \in dag : v.src = s /\ v.rnd = r

VertexOf(s, r) == CHOOSE v \in dag : v.src = s /\ v.rnd = r

\* Sources at round k reachable from the set S of sources at round j (j >= k).
RECURSIVE ReachSet(_, _, _)
ReachSet(S, j, k) ==
    IF j <= k THEN S
    ELSE ReachSet(UNION {VertexOf(s, j).edges : s \in S}, j - 1, k)

Reachable(r1, r2) ==   \* leader vertex of r2 reachable from leader vertex of r1
    Leader(r2) \in ReachSet({Leader(r1)}, r1, r2)

LastCommitted(p) == IF log[p] = <<>> THEN 0 ELSE log[p][Len(log[p])]

\* Indirectly committed leaders, ordered by round.
RECURSIVE Chain(_, _, _)
Chain(anchor, k, last) ==
    IF k <= last THEN <<>>
    ELSE IF HasVertex(Leader(k), k) /\ Reachable(anchor, k)
         THEN Chain(k, k - 1, last) \o <<k>>
         ELSE Chain(anchor, k - 1, last)

Supporters(r) ==
    {v.src : v \in {w \in dag : w.rnd = r + 1 /\ Leader(r) \in w.edges}}

-------------------------------------------------------------------------------
Init ==
    /\ round = [p \in Correct |-> 0]
    /\ dag   = {[src |-> s, rnd |-> 0, edges |-> {}] : s \in N}
    /\ log   = [p \in Correct |-> <<>>]
    /\ gst   = FALSE

\* A correct node creates its vertex for the next round.
Advance(p) ==
    LET r    == round[p]
        Prev == SrcsAt(r)
    IN /\ r < MaxRound
       /\ Prev \in Quorums
       /\ (gst /\ Leader(r) \in Correct) => Leader(r) \in Prev
       /\ dag' = dag \cup {[src |-> p, rnd |-> r + 1, edges |-> Prev]}
       /\ round' = [round EXCEPT ![p] = r + 1]
       /\ UNCHANGED <<log, gst>>

\* A Byzantine node creates an arbitrary (but valid) vertex.
ByzVertex(b, r) ==
    /\ ~HasVertex(b, r)
    /\ \E E \in SUBSET SrcsAt(r - 1) :
          /\ E \in Quorums
          /\ dag' = dag \cup {[src |-> b, rnd |-> r, edges |-> E]}
    /\ UNCHANGED <<round, log, gst>>

\* Direct commit of the leader vertex of round r.
Commit(p, r) ==
    /\ r > LastCommitted(p)
    /\ HasVertex(Leader(r), r)
    /\ Supporters(r) \in Quorums
    /\ log' = [log EXCEPT ![p] = log[p] \o Chain(r, r - 1, LastCommitted(p)) \o <<r>>]
    /\ UNCHANGED <<round, dag, gst>>

ReachGST ==
    /\ ~gst
    /\ gst' = TRUE
    /\ UNCHANGED <<round, dag, log>>

Done ==
    /\ \A p \in Correct : round[p] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Correct : Advance(p)
    \/ \E b \in Byz, r \in 1..MaxRound : ByzVertex(b, r)
    \/ \E p \in Correct, r \in 1..(MaxRound - 1) : Commit(p, r)
    \/ ReachGST
    \/ Done

Spec == Init /\ [][Next]_vars

TerminatingSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ReachGST)
    /\ \A p \in Correct : WF_vars(Advance(p))
    /\ \A p \in Correct : WF_vars(\E r \in 1..(MaxRound - 1) : Commit(p, r))

-------------------------------------------------------------------------------
TypeOK ==
    /\ round \in [Correct -> 0..MaxRound]
    /\ dag \subseteq Vertex
    /\ log \in [Correct -> Seq(1..MaxRound)]
    /\ gst \in BOOLEAN

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Agreement ==
    \A p, q \in Correct : IsPrefix(log[p], log[q]) \/ IsPrefix(log[q], log[p])

Liveness == <>(\A p \in Correct : round[p] = MaxRound)

StateConstraint ==
    /\ \A p \in Correct : round[p] <= MaxRound
    /\ \A p \in Correct : Len(log[p]) <= MaxRound

=============================================================================