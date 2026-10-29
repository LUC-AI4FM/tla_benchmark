---------------------------- MODULE GraphReachability ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes,      \* finite set of graph nodes
          Sources     \* a given source set of nodes

ASSUME NodesFinite  == IsFiniteSet(Nodes)
ASSUME NodesBigEnough == Cardinality(Nodes) >= 2
ASSUME SourcesOK    == Sources \subseteq Nodes

VARIABLES succ,   \* succ[n] : set of outgoing neighbors of node n
          reach,  \* reach[v] : computed set of nodes reachable from v
          phase   \* "init" -> "chosen" -> "evaluated"

vars == <<succ, reach, phase>>

N == Cardinality(Nodes)

-----------------------------------------------------------------------------
(* Candidate outgoing-neighbor relations                                     *)
-----------------------------------------------------------------------------

\* Sets of exactly two distinct nodes
TwoSubsets == {S \in SUBSET Nodes : Cardinality(S) = 2}

\* Relations where every node has exactly two distinct successors
TwoSuccRelations == [Nodes -> TwoSubsets]

\* Relations where any node may have any successors, including none
AnyRelations == [Nodes -> SUBSET Nodes]

-----------------------------------------------------------------------------
(* Reachability, defined two ways                                            *)
-----------------------------------------------------------------------------

\* Candidate paths: sequences of nodes of length 1..N
Paths == UNION { [1..k -> Nodes] : k \in 1..N }

\* p is a path that follows the outgoing edges of relation g
IsPath(g, p) ==
    \A i \in 1..(Len(p) - 1) : p[i+1] \in g[p[i]]

\* Specification of reachability: there exists a finite path from v to u.
\* A node is reachable from itself via the length-1 path.
PathReachable(g, v, u) ==
    \E p \in Paths : /\ p[1] = v
                     /\ p[Len(p)] = u
                     /\ IsPath(g, p)

\* Computation of reachability as a least fixed point (transitive closure)
RECURSIVE Closure(_, _)
Closure(g, S) ==
    LET T == S \cup UNION { g[n] : n \in S }
    IN  IF T = S THEN S ELSE Closure(g, T)

ReachFrom(g, v) == Closure(g, {v})

-----------------------------------------------------------------------------
(* Derived reachability queries (over the computed reach variable)           *)
-----------------------------------------------------------------------------

\* Pairs of nodes that are mutually reachable
MutuallyReachable ==
    { pr \in Nodes \X Nodes : pr[2] \in reach[pr[1]] /\ pr[1] \in reach[pr[2]] }

\* Nodes reachable from the given source set
ReachableFromSources == UNION { reach[s] : s \in Sources }

\* Nodes reachable from some, but not all, other nodes
SomeButNotAll ==
    { u \in Nodes :
        /\ \E v \in Nodes \ {u} : u \in reach[v]
        /\ \E v \in Nodes \ {u} : u \notin reach[v] }

\* Predicates whose satisfiability we want to explore
EveryNodeTwoSucc ==
    \A n \in Nodes : Cardinality(succ[n]) = 2 /\ succ[n] \subseteq Nodes

SomeNodeReachableFromAll ==
    \E u \in Nodes : \A v \in Nodes \ {u} : u \in reach[v]

SomeNodeReachableFromSomeButNotAll == SomeButNotAll # {}

-----------------------------------------------------------------------------
(* Initial state and actions                                                 *)
-----------------------------------------------------------------------------

Init ==
    /\ succ  = [n \in Nodes |-> {}]
    /\ reach = [n \in Nodes |-> {}]
    /\ phase = "init"

\* Nondeterministically choose a relation with exactly two successors per node
ChooseTwo ==
    /\ phase = "init"
    /\ succ' \in TwoSuccRelations
    /\ phase' = "chosen"
    /\ UNCHANGED reach

\* Nondeterministically choose an arbitrary relation (some nodes may have no edges)
ChooseAny ==
    /\ phase = "init"
    /\ succ' \in AnyRelations
    /\ phase' = "chosen"
    /\ UNCHANGED reach

Choose == ChooseTwo \/ ChooseAny

\* Evaluate reachability for every node under the chosen relation
Evaluate ==
    /\ phase = "chosen"
    /\ reach' = [v \in Nodes |-> ReachFrom(succ, v)]
    /\ phase' = "evaluated"
    /\ UNCHANGED succ

\* Terminal stuttering once evaluation is complete
Done ==
    /\ phase = "evaluated"
    /\ UNCHANGED vars

Next == Choose \/ Evaluate \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Choose) /\ WF_vars(Evaluate)

-----------------------------------------------------------------------------
(* Safety invariants                                                         *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ succ  \in [Nodes -> SUBSET Nodes]
    /\ reach \in [Nodes -> SUBSET Nodes]
    /\ phase \in {"init", "chosen", "evaluated"}

\* The fixed-point computation agrees with the path-based definition
ReachCorrect ==
    phase = "evaluated" =>
        \A v, u \in Nodes : (u \in reach[v]) <=> PathReachable(succ, v, u)

\* Every node reaches itself
ReachReflexive ==
    phase = "evaluated" => \A v \in Nodes : v \in reach[v]

\* Reachable sets are closed under successors
ReachClosed ==
    phase = "evaluated" =>
        \A v \in Nodes : \A n \in reach[v] : succ[n] \subseteq reach[v]

\* Reachability is transitive
ReachTransitive ==
    phase = "evaluated" =>
        \A v, w \in Nodes : w \in reach[v] => reach[w] \subseteq reach[v]

\* Source-set reachability is exactly path reachability from some source
SourceReachCorrect ==
    phase = "evaluated" =>
        \A u \in Nodes :
            (u \in ReachableFromSources) <=> \E s \in Sources : PathReachable(succ, s, u)

\* Mutual reachability is symmetric and agrees with path reachability
MutualReachCorrect ==
    phase = "evaluated" =>
        \A v, u \in Nodes :
            (<<v, u>> \in MutuallyReachable) <=>
                (PathReachable(succ, v, u) /\ PathReachable(succ, u, v))

\* "Some but not all" agrees with path reachability
SomeButNotAllCorrect ==
    phase = "evaluated" =>
        \A u \in Nodes :
            (u \in SomeButNotAll) <=>
                /\ \E v \in Nodes \ {u} : PathReachable(succ, v, u)
                /\ \E v \in Nodes \ {u} : ~PathReachable(succ, v, u)

\* Reach is not computed before evaluation
NoReachBeforeEval ==
    phase # "evaluated" => \A v \in Nodes : reach[v] = {}

-----------------------------------------------------------------------------
(* Existence checks: check these as invariants; a counterexample trace       *)
(* witnesses a configuration satisfying the corresponding predicate.        *)
-----------------------------------------------------------------------------

NoConfigEveryNodeTwoSucc ==
    ~(phase = "evaluated" /\ EveryNodeTwoSucc)

NoConfigSomeNodeReachableFromAll ==
    ~(phase = "evaluated" /\ SomeNodeReachableFromAll)

NoConfigSomeButNotAll ==
    ~(phase = "evaluated" /\ SomeNodeReachableFromSomeButNotAll)

NoConfigTwoSuccAndSomeButNotAll ==
    ~(phase = "evaluated" /\ EveryNodeTwoSucc /\ SomeNodeReachableFromSomeButNotAll)

-----------------------------------------------------------------------------
(* Temporal properties                                                       *)
-----------------------------------------------------------------------------

\* Evaluation eventually happens
EventuallyEvaluated == <>(phase = "evaluated")

\* Once a relation is chosen it never changes
SuccStable == [][phase # "init" => succ' = succ]_vars

\* Once evaluated, the results stay evaluated and correct forever
EvaluatedStable == [](phase = "evaluated" => [](phase = "evaluated"))

EventuallyCorrect ==
    <>[](phase = "evaluated" /\
         \A v, u \in Nodes : (u \in reach[v]) <=> PathReachable(succ, v, u))

\* Phases progress monotonically
PhaseOrder ==
    [][ \/ phase = phase'
        \/ (phase = "init"   /\ phase' = "chosen")
        \/ (phase = "chosen" /\ phase' = "evaluated") ]_vars

THEOREM Spec => [](TypeOK /\ ReachCorrect /\ ReachClosed /\ ReachTransitive)
=============================================================================