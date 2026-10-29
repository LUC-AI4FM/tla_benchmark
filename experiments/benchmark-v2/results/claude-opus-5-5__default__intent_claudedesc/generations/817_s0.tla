------------------------------ MODULE GraphReachability ------------------------------
(***************************************************************************)
(* Reachability analysis in a finite directed graph.                        *)
(*                                                                          *)
(*   Nodes : finite set of nodes                                            *)
(*   Succ  : successor function, Succ[n] = direct successors of n           *)
(*   Start : set of designated starting nodes                               *)
(*                                                                          *)
(* A worklist algorithm computes the set of nodes reachable from Start.     *)
(* Its result is compared against two independent characterizations:       *)
(*   (1) existence of a path of bounded length (at most |Nodes|), and       *)
(*   (2) a recursive fixpoint closure.                                      *)
(* Reachability is reflexive: a node is reachable from itself through a     *)
(* path of length 1.                                                        *)
(*                                                                          *)
(* A test configuration (TestNodes / TestSucc / TestStart) is provided.     *)
(* Every node in it has out-degree exactly 2, and nodes 4 and 5 are not     *)
(* reachable from node 1.  Example TLC model:                               *)
(*   Nodes <- TestNodes, Succ <- TestSucc, Start <- TestStart               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Succ, Start

ASSUME IsFiniteSet(Nodes)
ASSUME Succ \in [Nodes -> SUBSET Nodes]
ASSUME Start \subseteq Nodes

VARIABLES reached, frontier, steps

vars == <<reached, frontier, steps>>

(***************************************************************************)
(* Bound on exploration: no simple path is longer than |Nodes|.           *)
(***************************************************************************)
MaxLen == Cardinality(Nodes)

(***************************************************************************)
(* Reference characterization 1: bounded paths.                           *)
(***************************************************************************)
IsPath(p, n) ==
    \A i \in 1..(n - 1) : p[i + 1] \in Succ[p[i]]

PathFromTo(s, t) ==
    \E n \in 1..MaxLen :
        \E p \in [1..n -> Nodes] :
            /\ p[1] = s
            /\ p[n] = t
            /\ IsPath(p, n)

Reachable == { t \in Nodes : \E s \in Start : PathFromTo(s, t) }

(***************************************************************************)
(* Reference characterization 2: least fixpoint (reflexive-transitive     *)
(* closure). The recursion is well-founded on finite graphs because the    *)
(* argument strictly grows and is bounded by Nodes.                        *)
(***************************************************************************)
RECURSIVE Closure(_)
Closure(S) ==
    LET T == S \cup UNION { Succ[n] : n \in S }
    IN  IF T = S THEN S ELSE Closure(T)

ClosureReachable == Closure(Start)

(***************************************************************************)
(* Test graph: uniform out-degree 2, nodes 4 and 5 unreachable from 1.     *)
(***************************************************************************)
TestNodes == 1..5
TestSucc  == [n \in TestNodes |->
                CASE n = 1 -> {2, 3}
                  [] n = 2 -> {1, 3}
                  [] n = 3 -> {1, 2}
                  [] n = 4 -> {1, 5}
                  [] n = 5 -> {1, 4}]
TestStart == {1}

(***************************************************************************)
(* Worklist algorithm                                                      *)
(***************************************************************************)
Init ==
    /\ reached = Start
    /\ frontier = Start
    /\ steps = 0

Explore ==
    /\ frontier # {}
    /\ steps < MaxLen
    /\ \E n \in frontier :
         /\ reached' = reached \cup Succ[n]
         /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ reached)
         /\ steps' = steps + 1

Done ==
    /\ frontier = {}
    /\ UNCHANGED vars

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ reached \subseteq Nodes
    /\ frontier \subseteq reached
    /\ steps \in 0..MaxLen

\* Exploration stays within the bound tied to the number of nodes.
BoundedExploration == steps <= MaxLen

\* Soundness: every reported node is actually reachable via some path.
Soundness == reached \subseteq Reachable

\* Inductive helper: explored nodes have all successors already reached.
ClosedExplored ==
    \A n \in reached \ frontier : Succ[n] \subseteq reached

\* Start nodes are always reachable (base case / reflexivity).
BaseCase == Start \subseteq reached

\* Completeness: once the worklist is empty, every reachable node is reported.
Completeness == (frontier = {}) => (Reachable \subseteq reached)

\* Upon termination, the result equals both reference characterizations.
CorrectResult ==
    (frontier = {}) => (reached = Reachable /\ reached = ClosureReachable)

\* The two reference characterizations coincide (well-definedness).
CharacterizationsAgree == Reachable = ClosureReachable

\* Transitivity of the computed relation at termination.
Transitive ==
    (frontier = {}) =>
        \A a \in reached : \A b \in Succ[a] : b \in reached

Invariants ==
    /\ TypeOK
    /\ BoundedExploration
    /\ Soundness
    /\ ClosedExplored
    /\ BaseCase
    /\ Completeness
    /\ CorrectResult
    /\ CharacterizationsAgree
    /\ Transitive

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
Termination == <>(frontier = {})

EventuallyComplete == <>[](reached = Reachable)

THEOREM Spec => []Invariants
THEOREM Spec => Termination /\ EventuallyComplete
=====================================================================================