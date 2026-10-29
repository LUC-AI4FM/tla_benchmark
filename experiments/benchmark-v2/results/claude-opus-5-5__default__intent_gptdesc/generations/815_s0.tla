---------------------------- MODULE SyncReachability ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node,      \* fixed finite set of node identifiers
          Fanout     \* bound on number of distinct forwarding neighbors (e.g. 2)

ASSUME NodeAssump   == Node # {} /\ IsFiniteSet(Node)
ASSUME FanoutAssump == Fanout \in Nat /\ Fanout >= 1

VARIABLES nbrs,      \* nbrs[n]       : fixed set of outgoing neighbors of n
          known,     \* known[n]      : identifiers currently known by n
          sent,      \* sent[n]       : neighbors n forwarded to in the last round
          payload,   \* payload[n][m] : identifiers n sent to m in the last round
          done       \* termination detected (a full round produced no change)

vars == <<nbrs, known, sent, payload, done>>

Min(a, b) == IF a <= b THEN a ELSE b

Degree == Min(Fanout, Cardinality(Node) - 1)

----------------------------------------------------------------------------
(* Graph reachability over the neighbor relation *)

Succ(S) == UNION {nbrs[m] : m \in S}

RECURSIVE ReachIter(_, _)
ReachIter(S, k) == IF k = 0 THEN S ELSE ReachIter(S \cup Succ(S), k - 1)

\* Reach(n): nodes reachable from n (including n itself)
Reach(n) == ReachIter({n}, Cardinality(Node))

\* Sources(m): nodes whose identifier can flow to m
Sources(m) == {n \in Node : m \in Reach(n)}

\* Strongly connected component of n
SCC(n) == {m \in Node : m \in Reach(n) /\ n \in Reach(m)}

StronglyConnected == \A n \in Node : Reach(n) = Node

\* Knowledge that a full flooding round would produce
FullUpdate == [m \in Node |->
                 known[m] \cup UNION {known[n] : n \in {x \in Node : m \in nbrs[x]}}]

Quiescent == FullUpdate = known

----------------------------------------------------------------------------
TypeOK ==
  /\ nbrs    \in [Node -> SUBSET Node]
  /\ known   \in [Node -> SUBSET Node]
  /\ sent    \in [Node -> SUBSET Node]
  /\ payload \in [Node -> [Node -> SUBSET Node]]
  /\ done    \in BOOLEAN

Init ==
  /\ nbrs \in {f \in [Node -> SUBSET Node] :
                 \A n \in Node : /\ n \notin f[n]
                                 /\ Cardinality(f[n]) = Degree}
  /\ known   = [n \in Node |-> {n}]
  /\ sent    = [n \in Node |-> {}]
  /\ payload = [n \in Node |-> [m \in Node |-> {}]]
  /\ done    = FALSE

\* A synchronous round with nondeterministic forwarding: each node picks
\* a subset of its (bounded) neighbors and sends each a subset of what it knows.
Round ==
  /\ \E tgt \in [Node -> SUBSET Node] :
       /\ \A n \in Node : tgt[n] \subseteq nbrs[n]
       /\ \E pl \in [Node -> [Node -> SUBSET Node]] :
            /\ \A n, m \in Node :
                 pl[n][m] \subseteq (IF m \in tgt[n] THEN known[n] ELSE {})
            /\ known'   = [m \in Node |->
                             known[m] \cup UNION {pl[n][m] : n \in Node}]
            /\ sent'    = tgt
            /\ payload' = pl
  /\ UNCHANGED <<nbrs, done>>

\* A full flooding round: every node sends everything it knows to all neighbors.
\* If it produces no change, termination is detected.
FullRound ==
  /\ sent'    = nbrs
  /\ payload' = [n \in Node |-> [m \in Node |->
                    IF m \in nbrs[n] THEN known[n] ELSE {}]]
  /\ known'   = FullUpdate
  /\ done'    = (FullUpdate = known)
  /\ UNCHANGED nbrs

Next == Round \/ FullRound

\* Fair continual communication: full rounds cannot be postponed forever.
Fairness == WF_vars(FullRound)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Safety *)

NoSpuriousIds    == \A n \in Node : known[n] \subseteq Node

KnowsSelf        == \A n \in Node : n \in known[n]

BoundedNeighbors == \A n \in Node : /\ nbrs[n] \subseteq Node \ {n}
                                    /\ Cardinality(nbrs[n]) <= Fanout

BoundedForwarding == \A n \in Node : /\ sent[n] \subseteq nbrs[n]
                                     /\ Cardinality(sent[n]) <= Fanout

PayloadValid ==
  \A n, m \in Node : /\ payload[n][m] \subseteq known[n]
                     /\ (m \notin sent[n] => payload[n][m] = {})

\* Knowledge only flows along edges
KnowledgeSound == \A m \in Node : known[m] \subseteq Sources(m)

\* Termination detection is sound
DetectionSound == done => Quiescent

Safety == /\ TypeOK /\ NoSpuriousIds /\ KnowsSelf /\ BoundedNeighbors
          /\ BoundedForwarding /\ PayloadValid /\ KnowledgeSound
          /\ DetectionSound

\* Monotonic growth (action properties)
Monotonicity     == [][\A n \in Node : known[n] \subseteq known'[n]]_vars
NeighborsFixed   == [][nbrs' = nbrs]_vars
QuiescenceStable == [][Quiescent => known' = known]_vars
DoneStable       == [][done => (done' /\ known' = known)]_vars

----------------------------------------------------------------------------
(* Liveness *)

LearnsSCC == \A n \in Node : <>(SCC(n) \subseteq known[n])

LearnsAllSources == \A n \in Node : <>[](known[n] = Sources(n))

GlobalReachability == StronglyConnected => <>(\A n \in Node : known[n] = Node)

EventuallyQuiescent == <>[]Quiescent

TerminationDetected == <>done

QuiescentLeadsToDone == Quiescent ~> done

THEOREM Spec => []Safety
THEOREM Spec => Monotonicity /\ NeighborsFixed /\ QuiescenceStable /\ DoneStable
THEOREM Spec => LearnsSCC /\ LearnsAllSources /\ GlobalReachability
THEOREM Spec => EventuallyQuiescent /\ TerminationDetected
=============================================================================