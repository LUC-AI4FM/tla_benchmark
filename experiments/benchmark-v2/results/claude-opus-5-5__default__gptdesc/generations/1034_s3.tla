---------------------------- MODULE SailfishBounded ----------------------------
(***************************************************************************)
(* A small bounded configuration of the Sailfish DAG-based BFT protocol:   *)
(* three nodes, one of which (n3) is Byzantine.  Vertices are reliably      *)
(* broadcast, so a node has at most one vertex per round.                   *)
(*                                                                         *)
(* A correct node in round r creates a round r+1 vertex once it has         *)
(* received a quorum of round-r vertices and either:                        *)
(*   - the round-r leader vertex, or                                        *)
(*   - a quorum of timeouts for round r.                                    *)
(*                                                                         *)
(* A leader vertex of round r is committed once a quorum of round-(r+1)     *)
(* vertices point to it.  Committing it also orders the earlier             *)
(* uncommitted leader vertices that are reachable from it.                  *)
(*                                                                         *)
(* Before GST, correct nodes may time out at any moment.  After GST,        *)
(* correct nodes only time out on rounds whose leader is Byzantine.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS GST, MaxRound

ASSUME GST \in Nat /\ MaxRound \in Nat \ {0}

\* Concrete node sets.
Nodes   == {"n1", "n2", "n3"}
Byz     == {"n3"}
Correct == Nodes \ Byz

\* Quorum and blocking-set predicates (n = 3, f = 1).
IsQuorum(Q)   == Q \subseteq Nodes /\ Cardinality(Q) >= 2
IsBlocking(B) == B \subseteq Nodes /\ Cardinality(B) >= 1 /\ B \cap Correct # {}

\* Round-robin leader schedule.
LeaderSeq == <<"n1", "n2", "n3">>
Leader(r) == LeaderSeq[(r % 3) + 1]

VARIABLES round, vertices, received, timeouts, log, clock
vars == <<round, vertices, received, timeouts, log, clock>>

Genesis == {[src |-> n, rnd |-> 0, edges |-> {}] : n \in Nodes}

Vertex == [src : Nodes, rnd : 0..(MaxRound + 1), edges : SUBSET Nodes]

TypeOK ==
    /\ round \in [Correct -> Nat]
    /\ vertices \subseteq Vertex
    /\ received \in [Correct -> SUBSET Vertex]
    /\ timeouts \subseteq [src : Nodes, rnd : Nat]
    /\ log \in [Correct -> Seq(Nat)]
    /\ clock \in 0..GST

-----------------------------------------------------------------------------
\* Helpers

SourcesAt(S, r) == {v.src : v \in {w \in S : w.rnd = r}}

LeaderVertex(S, r) == {v \in S : v.rnd = r /\ v.src = Leader(r)}

TimeoutSrcs(r) == {t.src : t \in {u \in timeouts : u.rnd = r}}

Parents(S, v) == {p \in S : p.rnd = v.rnd - 1 /\ p.src \in v.edges}

RECURSIVE Anc(_, _)
Anc(S, v) == IF v.rnd = 0 THEN {v}
             ELSE {v} \cup UNION {Anc(S, p) : p \in Parents(S, v)}

RECURSIVE SetToSeq(_)
SetToSeq(S) == IF S = {} THEN << >>
               ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y
                    IN  <<m>> \o SetToSeq(S \ {m})

LastCommitted(n) == IF log[n] = << >> THEN 0 ELSE log[n][Len(log[n])]

-----------------------------------------------------------------------------
Init ==
    /\ round    = [n \in Correct |-> 0]
    /\ vertices = Genesis
    /\ received = [n \in Correct |-> Genesis]
    /\ timeouts = {}
    /\ log      = [n \in Correct |-> << >>]
    /\ clock    = 0

Tick ==
    /\ clock < GST
    /\ clock' = clock + 1
    /\ UNCHANGED <<round, vertices, received, timeouts, log>>

CorrectAdvance(n) ==
    LET r   == round[n]
        Src == SourcesAt(received[n], r)
        v   == [src |-> n, rnd |-> r + 1, edges |-> Src]
    IN  /\ IsQuorum(Src)
        /\ \/ LeaderVertex(received[n], r) # {}
           \/ IsQuorum(TimeoutSrcs(r))
        /\ vertices' = vertices \cup {v}
        /\ received' = [received EXCEPT ![n] = @ \cup {v}]
        /\ round'    = [round EXCEPT ![n] = r + 1]
        /\ UNCHANGED <<timeouts, log, clock>>

Receive(n, v) ==
    /\ v \in vertices \ received[n]
    /\ v.edges \subseteq SourcesAt(received[n], v.rnd - 1)
    /\ received' = [received EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<round, vertices, timeouts, log, clock>>

CorrectTimeout(n) ==
    LET r == round[n] IN
    /\ LeaderVertex(received[n], r) = {}
    /\ [src |-> n, rnd |-> r] \notin timeouts
    /\ clock < GST \/ Leader(r) \in Byz
    /\ timeouts' = timeouts \cup {[src |-> n, rnd |-> r]}
    /\ UNCHANGED <<round, vertices, received, log, clock>>

ByzVertex(b, r, E) ==
    /\ ~\E w \in vertices : w.src = b /\ w.rnd = r
    /\ IsQuorum(E)
    /\ E \subseteq SourcesAt(vertices, r - 1)
    /\ vertices' = vertices \cup {[src |-> b, rnd |-> r, edges |-> E]}
    /\ UNCHANGED <<round, received, timeouts, log, clock>>

ByzTimeout(b, r) ==
    /\ [src |-> b, rnd |-> r] \notin timeouts
    /\ timeouts' = timeouts \cup {[src |-> b, rnd |-> r]}
    /\ UNCHANGED <<round, vertices, received, log, clock>>

Commit(n) ==
    \E lv \in received[n] :
        LET r == lv.rnd
            S == received[n]
            Supporters == {w.src : w \in {x \in S : x.rnd = r + 1 /\ lv.src \in x.edges}}
            A == Anc(S, lv)
            Rounds == {k \in (LastCommitted(n) + 1)..r :
                         \E u \in A : u.rnd = k /\ u.src = Leader(k)}
        IN  /\ r >= 1
            /\ lv.src = Leader(r)
            /\ r > LastCommitted(n)
            /\ IsQuorum(Supporters)
            /\ log' = [log EXCEPT ![n] = @ \o SetToSeq(Rounds)]
            /\ UNCHANGED <<round, vertices, received, timeouts, clock>>

Next ==
    \/ Tick
    \/ \E n \in Correct : CorrectAdvance(n) \/ CorrectTimeout(n) \/ Commit(n)
    \/ \E n \in Correct, v \in vertices : Receive(n, v)
    \/ \E b \in Byz, r \in 1..(MaxRound + 1), E \in SUBSET Nodes : ByzVertex(b, r, E)
    \/ \E b \in Byz, r \in 0..MaxRound : ByzTimeout(b, r)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Correct :
        /\ WF_vars(CorrectAdvance(n))
        /\ WF_vars(CorrectTimeout(n))
        /\ WF_vars(Commit(n))
        /\ WF_vars(\E v \in vertices : Receive(n, v))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* State constraint that bounds the explored rounds of non-faulty nodes.
StateConstraint == \A n \in Correct : round[n] <= MaxRound

\* Terminating variant of the behavior specification.
Done == \A n \in Correct : round[n] = MaxRound

Terminate == Done /\ UNCHANGED vars

TermNext ==
    \/ (\A n \in Correct : round[n] <= MaxRound) /\ Next
    \/ Terminate

TermSpec == Init /\ [][TermNext]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

Prefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Consistency ==
    \A n, m \in Correct : Prefix(log[n], log[m]) \/ Prefix(log[m], log[n])

NoDuplicateVertex ==
    \A v, w \in vertices : (v.src = w.src /\ v.rnd = w.rnd) => v = w

LogIsLeaderRounds ==
    \A n \in Correct : \A i \in 1..Len(log[n]) : log[n][i] >= 1

LogIncreasing ==
    \A n \in Correct : \A i, j \in 1..Len(log[n]) : i < j => log[n][i] < log[n][j]

\* Liveness

AllCorrectEventuallyFinish == <>Done

EventuallySomeCommit == <>(\E n \in Correct : Len(log[n]) > 0)

-----------------------------------------------------------------------------
\* Deliberately false predicates, used to make TLC produce interesting
\* counterexample executions.

\* Violated when all correct nodes reach the final round.
NotAllCorrectFinished == ~Done

\* Violated when some correct node commits something.
NoCommittedEntries == \A n \in Correct : Len(log[n]) = 0

\* Violated when some correct node commits at least two entries.
LogShorterThanTwo == \A n \in Correct : Len(log[n]) < 2

\* Violated when a Byzantine leader's vertex is committed.
NoByzLeaderCommitted ==
    \A n \in Correct : \A i \in 1..Len(log[n]) : Leader(log[n][i]) \notin Byz

\* Temporal: violated when all correct nodes finish having committed something.
NeverFinishWithCommit ==
    [](~(Done /\ \A n \in Correct : Len(log[n]) > 0))

=============================================================================