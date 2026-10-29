---- MODULE GraphReachability ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* A graph is a record [node, init, trans, bad] where:                     *)
(*   node  : finite set of nodes                                           *)
(*   init  : set of initial nodes (subset of node)                         *)
(*   trans : set of labeled transitions [src, label, dst], where dst is    *)
(*           the (possibly empty) set of possible successor nodes          *)
(*   bad   : set of designated bad nodes                                   *)
(***************************************************************************)

VARIABLE checked

WellFormed(G) ==
    /\ G.init \subseteq G.node
    /\ G.bad \subseteq G.node
    /\ \A t \in G.trans : t.src \in G.node /\ t.dst \subseteq G.node

\* Successors of a node through any labeled transition
Succ(G, n) == UNION { t.dst : t \in { u \in G.trans : u.src = n } }

\* Image of a set of nodes
Post(G, S) == UNION { Succ(G, n) : n \in S }

(***************************************************************************)
(* Path semantics: a finite, non-empty sequence of nodes starting in an    *)
(* initial node whose consecutive elements are related by a transition.    *)
(***************************************************************************)
IsPath(G, p) ==
    /\ Len(p) >= 1
    /\ \A i \in 1..Len(p) : p[i] \in G.node
    /\ p[1] \in G.init
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ(G, p[i])

Last(p) == p[Len(p)]

\* Candidate sequences bounded by the number of nodes (enough for simple paths)
BoundedSeqs(G) == UNION { [1..k -> G.node] : k \in 1..Cardinality(G.node) }

Paths(G) == { p \in BoundedSeqs(G) : IsPath(G, p) }

\* Path-based reachability (semantic definition)
PathReachable(G) == { n \in G.node : \E p \in Paths(G) : Last(p) = n }

(***************************************************************************)
(* Reachability as a fixpoint of the successor relation (the analysis      *)
(* result). No particular algorithm is prescribed: this is just the        *)
(* least set containing init closed under Post.                            *)
(***************************************************************************)
RECURSIVE Iterate(_, _, _)
Iterate(G, S, k) ==
    IF k = 0 THEN S ELSE Iterate(G, S \cup Post(G, S), k - 1)

Reachable(G) == Iterate(G, G.init, Cardinality(G.node))

\* Violation detection
Violated(G) == Reachable(G) \cap G.bad # {}

\* Counterexample: some path to a bad node, or <<>> if none exists
CounterExample(G) ==
    IF \E p \in Paths(G) : Last(p) \in G.bad
       THEN CHOOSE p \in Paths(G) : Last(p) \in G.bad
       ELSE << >>

(***************************************************************************)
(* Correctness obligations                                                 *)
(***************************************************************************)
\* (1) any returned counterexample is a valid path ending in a bad node
CexValid(G) ==
    LET ce == CounterExample(G) IN
    ce # << >> => /\ IsPath(G, ce)
                  /\ ce[1] \in G.init
                  /\ Last(ce) \in G.bad

\* (2) no counterexample implies no bad node reachable
NoCexSafe(G) ==
    CounterExample(G) = << >> => Reachable(G) \cap G.bad = {}

\* Violation detected iff counterexample produced
CexComplete(G) == Violated(G) <=> (CounterExample(G) # << >>)

\* (3) reachability sound and complete w.r.t. finite path semantics
ReachSound    == \A G \in {} : TRUE
ReachSoundG(G)    == Reachable(G) \subseteq PathReachable(G)
ReachCompleteG(G) == PathReachable(G) \subseteq Reachable(G)

\* Reachable set is the least closed set containing init
ReachLeastFixpoint(G) ==
    /\ G.init \subseteq Reachable(G)
    /\ Post(G, Reachable(G)) \subseteq Reachable(G)
    /\ \A S \in SUBSET G.node :
          (G.init \subseteq S /\ Post(G, S) \subseteq S) => Reachable(G) \subseteq S

Correct(G) ==
    /\ WellFormed(G)
    /\ CexValid(G)
    /\ NoCexSafe(G)
    /\ CexComplete(G)
    /\ ReachSoundG(G)
    /\ ReachCompleteG(G)
    /\ ReachLeastFixpoint(G)

(***************************************************************************)
(* Independent test graphs                                                 *)
(***************************************************************************)
\* Empty graph
G1 == [node |-> {}, init |-> {}, trans |-> {}, bad |-> {}]

\* Single initial node, no outgoing transitions, itself bad
G2 == [node |-> {1}, init |-> {1}, trans |-> {}, bad |-> {1}]

\* Chain with a transition to no successor; bad node unreachable
G3 == [node  |-> {1, 2, 3, 4},
       init  |-> {1},
       trans |-> { [src |-> 1, label |-> "a", dst |-> {2}],
                   [src |-> 2, label |-> "b", dst |-> {}],
                   [src |-> 2, label |-> "c", dst |-> {3}] },
       bad   |-> {4}]

\* Multi-sink structure with nondeterministic branching; bad reachable
G4 == [node  |-> {1, 2, 3, 4},
       init  |-> {1},
       trans |-> { [src |-> 1, label |-> "a", dst |-> {2, 3}],
                   [src |-> 1, label |-> "b", dst |-> {4}] },
       bad   |-> {3}]

\* Strongly connected component with an exit to a bad node,
\* plus an unreachable bad node
G5 == [node  |-> {1, 2, 3, 4, 5},
       init  |-> {1},
       trans |-> { [src |-> 1, label |-> "a", dst |-> {2}],
                   [src |-> 2, label |-> "a", dst |-> {3}],
                   [src |-> 3, label |-> "a", dst |-> {1}],
                   [src |-> 3, label |-> "b", dst |-> {4}],
                   [src |-> 5, label |-> "a", dst |-> {1}] },
       bad   |-> {4, 5}]

\* Non-empty graph with no initial nodes
G6 == [node  |-> {1, 2},
       init  |-> {},
       trans |-> { [src |-> 1, label |-> "a", dst |-> {2}] },
       bad   |-> {2}]

\* SCC with no path to bad
G7 == [node  |-> {1, 2, 3},
       init  |-> {1, 2},
       trans |-> { [src |-> 1, label |-> "a", dst |-> {2}],
                   [src |-> 2, label |-> "a", dst |-> {1}] },
       bad   |-> {3}]

TestGraphs == {G1, G2, G3, G4, G5, G6, G7}

\* Expected outcomes on the concrete test graphs
ExpectedOutcomes ==
    /\ Reachable(G1) = {}        /\ ~Violated(G1)
    /\ Reachable(G2) = {1}       /\ Violated(G2)
    /\ Reachable(G3) = {1, 2, 3} /\ ~Violated(G3)
    /\ Reachable(G4) = {1, 2, 3, 4} /\ Violated(G4)
    /\ Reachable(G5) = {1, 2, 3, 4} /\ Violated(G5)
    /\ Reachable(G6) = {}        /\ ~Violated(G6)
    /\ Reachable(G7) = {1, 2}    /\ ~Violated(G7)

TestCase ==
    /\ \A G \in TestGraphs : Correct(G)
    /\ ExpectedOutcomes

ASSUME TestCase

(***************************************************************************)
(* Trivial behavior so TestCase can also be checked as an invariant        *)
(***************************************************************************)
Init == checked = FALSE
Next == checked' = TRUE
Spec == Init /\ [][Next]_checked

====