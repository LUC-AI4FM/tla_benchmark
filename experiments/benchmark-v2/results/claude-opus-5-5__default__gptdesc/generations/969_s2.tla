------------------------------ MODULE TestGraphs ------------------------------
(***************************************************************************)
(* Static data library of directed state graphs for testing model-checker *)
(* specifications such as TLCMC and MCReachability.                       *)
(*                                                                         *)
(* Each graph is a record with these fields:                               *)
(*   states   : the set of states, numbered 1..N                           *)
(*   initials : the set of initial states                                  *)
(*   edges    : a sequence of successor sets, where edges[s] is the set    *)
(*              of successors of state s                                   *)
(*                                                                         *)
(* For each graph Gi, the operator Vi defines the violating states and the *)
(* operator Ci defines an example counterexample path, which is a          *)
(* sequence of states.                                                     *)
(*                                                                         *)
(* The module has no variables, actions, temporal specification, fairness *)
(* or proofs. The test case is selected by the IO environment variable     *)
(* GRAPH. If GRAPH is not set, graph 7 is used.                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, IOUtils

-------------------------------------------------------------------------------
(* Graph 1: a single initial state with no successors (deadlock). *)
G1 == [ states   |-> 1..1,
        initials |-> {1},
        edges    |-> << {} >> ]
V1 == {}
C1 == << >>

(* Graph 2: a linear chain 1 -> 2 -> 3, where 3 loops on itself. *)
G2 == [ states   |-> 1..3,
        initials |-> {1},
        edges    |-> << {2}, {3}, {3} >> ]
V2 == {3}
C2 == << 1, 2, 3 >>

(* Graph 3: two initial states that converge on state 3. *)
G3 == [ states   |-> 1..3,
        initials |-> {1, 2},
        edges    |-> << {3}, {3}, {1} >> ]
V3 == {3}
C3 == << 1, 3 >>

(* Graph 4: a simple cycle 1 -> 2 -> 3 -> 1 with no violations. *)
G4 == [ states   |-> 1..3,
        initials |-> {1},
        edges    |-> << {2}, {3}, {1} >> ]
V4 == {}
C4 == << >>

(* Graph 5: a diamond 1 -> {2,3} -> 4, where 4 is a deadlock state. *)
G5 == [ states   |-> 1..4,
        initials |-> {1},
        edges    |-> << {2, 3}, {4}, {4}, {} >> ]
V5 == {4}
C5 == << 1, 2, 4 >>

(* Graph 6: the violating state lies in an unreachable component. *)
G6 == [ states   |-> 1..4,
        initials |-> {1},
        edges    |-> << {2}, {1}, {4}, {3} >> ]
V6 == {4}
C6 == << >>

(* Graph 7 (default): branching graph with a back edge and a sink loop. *)
G7 == [ states   |-> 1..6,
        initials |-> {1},
        edges    |-> << {2, 3}, {4}, {5}, {1}, {6}, {6} >> ]
V7 == {6}
C7 == << 1, 3, 5, 6 >>

(* Graph 8: the initial state is itself violating and has a self loop. *)
G8 == [ states   |-> 1..1,
        initials |-> {1},
        edges    |-> << {1} >> ]
V8 == {1}
C8 == << 1 >>

-------------------------------------------------------------------------------
(* Well-formedness of a graph record. *)
WellFormed(g) ==
    /\ g.initials \subseteq g.states
    /\ Len(g.edges) = Cardinality(g.states)
    /\ \A s \in g.states : g.edges[s] \subseteq g.states

(* A counterexample is valid if it is a path from an initial state to a   *)
(* violating state. The empty sequence means "no counterexample".         *)
IsPath(g, p) ==
    /\ Len(p) > 0
    /\ \A i \in 1..Len(p) : p[i] \in g.states
    /\ p[1] \in g.initials
    /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in g.edges[p[i]]

ValidCounterexample(g, v, c) ==
    \/ c = << >>
    \/ IsPath(g, c) /\ c[Len(c)] \in v

-------------------------------------------------------------------------------
(* Selection of the test case through the IO environment variable GRAPH. *)
GraphName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

MkCase(g, v, c) == [ graph |-> g, violations |-> v, counterexample |-> c ]

TestCase ==
    CASE GraphName = "1" -> MkCase(G1, V1, C1)
      [] GraphName = "2" -> MkCase(G2, V2, C2)
      [] GraphName = "3" -> MkCase(G3, V3, C3)
      [] GraphName = "4" -> MkCase(G4, V4, C4)
      [] GraphName = "5" -> MkCase(G5, V5, C5)
      [] GraphName = "6" -> MkCase(G6, V6, C6)
      [] GraphName = "8" -> MkCase(G8, V8, C8)
      [] OTHER           -> MkCase(G7, V7, C7)

Graph          == TestCase.graph
Violations     == TestCase.violations
Counterexample == TestCase.counterexample

(* Static sanity check of the selected test case. *)
TestCaseOK ==
    /\ WellFormed(Graph)
    /\ Violations \subseteq Graph.states
    /\ ValidCounterexample(Graph, Violations, Counterexample)

===============================================================================