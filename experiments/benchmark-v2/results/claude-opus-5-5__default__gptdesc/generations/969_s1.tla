---------------------------- MODULE TestGraphs ----------------------------
(***************************************************************************)
(* A static library of directed state graphs used to test model-checker    *)
(* specifications such as TLCMC and MCReachability.                        *)
(*                                                                         *)
(* Each graph is a record with the fields:                                 *)
(*   states   : the set of states (state numbers 1..N),                    *)
(*   initials : the set of initial states,                                 *)
(*   actions  : a sequence of successor-state sets, where actions[s] is    *)
(*              the set of successors of state s.                          *)
(*                                                                         *)
(* For each graph, separate operators give the set of violating states     *)
(* and the set of example counterexample paths. A path is a sequence of    *)
(* states that starts in an initial state, follows edges, and ends in a    *)
(* violating state.                                                        *)
(*                                                                         *)
(* The module has no variables, actions, temporal specification, fairness  *)
(* or proofs. It is a data library. One test case is selected by the IO    *)
(* environment variable GRAPH. If GRAPH is not set, graph 7 is selected.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, IOUtils, TLC

---------------------------------------------------------------------------
(* Graph 1: a simple chain with no violations.                             *)
Graph1 == [states   |-> 1..3,
           initials |-> {1},
           actions  |-> << {2}, {3}, {} >>]
Violations1     == {}
Counterexample1 == {}

(* Graph 2: a cycle with a violation at the end of the cycle.              *)
Graph2 == [states   |-> 1..3,
           initials |-> {1},
           actions  |-> << {2}, {3}, {1} >>]
Violations2     == {3}
Counterexample2 == { <<1, 2, 3>> }

(* Graph 3: a single state with a self loop that is a violation.           *)
Graph3 == [states   |-> 1..1,
           initials |-> {1},
           actions  |-> << {1} >>]
Violations3     == {1}
Counterexample3 == { <<1>> }

(* Graph 4: two initial states with disjoint components.                   *)
Graph4 == [states   |-> 1..4,
           initials |-> {1, 3},
           actions  |-> << {2}, {}, {4}, {} >>]
Violations4     == {4}
Counterexample4 == { <<3, 4>> }

(* Graph 5: a diamond with two equally short counterexamples.              *)
Graph5 == [states   |-> 1..4,
           initials |-> {1},
           actions  |-> << {2, 3}, {4}, {4}, {} >>]
Violations5     == {4}
Counterexample5 == { <<1, 2, 4>>, <<1, 3, 4>> }

(* Graph 6: the violating state is unreachable.                            *)
Graph6 == [states   |-> 1..4,
           initials |-> {1},
           actions  |-> << {2}, {1}, {4}, {3} >>]
Violations6     == {3}
Counterexample6 == {}

(* Graph 7: a larger graph with branching, joins and a back edge.          *)
Graph7 == [states   |-> 1..6,
           initials |-> {1},
           actions  |-> << {2, 3}, {4}, {5}, {6}, {6}, {1} >>]
Violations7     == {6}
Counterexample7 == { <<1, 2, 4, 6>>, <<1, 3, 5, 6>> }

(* Graph 8: an initial state is itself a violation.                        *)
Graph8 == [states   |-> 1..2,
           initials |-> {1, 2},
           actions  |-> << {2}, {1} >>]
Violations8     == {2}
Counterexample8 == { <<2>> }

(* Graph 9: no initial states, so nothing is reachable.                    *)
Graph9 == [states   |-> 1..2,
           initials |-> {},
           actions  |-> << {2}, {} >>]
Violations9     == {1}
Counterexample9 == {}

(* Graph 10: a long linear chain with a violation at the end.              *)
Graph10 == [states   |-> 1..10,
            initials |-> {1},
            actions  |-> [i \in 1..10 |-> IF i < 10 THEN {i + 1} ELSE {}]]
Violations10     == {10}
Counterexample10 == { [i \in 1..10 |-> i] }

---------------------------------------------------------------------------
(* Bundling a graph with its violations and counterexamples.               *)
TestCase(g, v, c) == [graph |-> g, violations |-> v, counterexamples |-> c]

TestCases ==
    << TestCase(Graph1,  Violations1,  Counterexample1),
       TestCase(Graph2,  Violations2,  Counterexample2),
       TestCase(Graph3,  Violations3,  Counterexample3),
       TestCase(Graph4,  Violations4,  Counterexample4),
       TestCase(Graph5,  Violations5,  Counterexample5),
       TestCase(Graph6,  Violations6,  Counterexample6),
       TestCase(Graph7,  Violations7,  Counterexample7),
       TestCase(Graph8,  Violations8,  Counterexample8),
       TestCase(Graph9,  Violations9,  Counterexample9),
       TestCase(Graph10, Violations10, Counterexample10) >>

(* Map of names, as given in the GRAPH environment variable, to indices.   *)
GraphNames ==
    [n \in {"1","2","3","4","5","6","7","8","9","10"} |->
        CASE n = "1"  -> 1  [] n = "2" -> 2 [] n = "3" -> 3
          [] n = "4"  -> 4  [] n = "5" -> 5 [] n = "6" -> 6
          [] n = "7"  -> 7  [] n = "8" -> 8 [] n = "9" -> 9
          [] n = "10" -> 10]

DefaultGraph == "7"

(* Name of the selected test case. Defaults to graph 7 if GRAPH is unset.  *)
SelectedName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE DefaultGraph

SelectedIndex ==
    IF SelectedName \in DOMAIN GraphNames
    THEN GraphNames[SelectedName]
    ELSE Assert(FALSE, "Unknown value for the GRAPH environment variable")

Selected == TestCases[SelectedIndex]

(* Operators exported to model-checker specifications under test.          *)
Graph           == Selected.graph
States          == Graph.states
Initials        == Graph.initials
Successors(s)   == Graph.actions[s]
Violations      == Selected.violations
Counterexamples == Selected.counterexamples

---------------------------------------------------------------------------
(* Sanity checks on the test data.                                         *)
IsGraph(g) ==
    /\ g.initials \subseteq g.states
    /\ DOMAIN g.actions = g.states
    /\ \A s \in g.states : g.actions[s] \subseteq g.states

IsPath(g, p) ==
    /\ Len(p) > 0
    /\ p[1] \in g.initials
    /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in g.actions[p[i]]

IsCounterexample(g, v, p) ==
    IsPath(g, p) /\ p[Len(p)] \in v

WellFormed(t) ==
    /\ IsGraph(t.graph)
    /\ t.violations \subseteq t.graph.states
    /\ \A p \in t.counterexamples : IsCounterexample(t.graph, t.violations, p)

AllWellFormed == \A i \in DOMAIN TestCases : WellFormed(TestCases[i])

SelectedWellFormed == WellFormed(Selected)

=============================================================================