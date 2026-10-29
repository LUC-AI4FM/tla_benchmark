------------------------------- MODULE TestGraphs -------------------------------
(***************************************************************************)
(* A static data library of directed state graphs, their violating states *)
(* and example counterexample paths. It is used to test model-checker     *)
(* specifications such as TLCMC and MCReachability.                       *)
(*                                                                         *)
(* Each graph is a record with these fields:                               *)
(*   states   : the set of states, which are 1..N                          *)
(*   initials : the set of initial states                                  *)
(*   actions  : a sequence of successor-state sets, where actions[i] is    *)
(*              the set of successors of state i                           *)
(*                                                                         *)
(* The test case is chosen by the environment variable GRAPH. If GRAPH is  *)
(* not set, graph 7 is used.                                               *)
(*                                                                         *)
(* The module has no variables, actions, temporal specification, fairness  *)
(* or proofs.                                                              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, IOUtils

-----------------------------------------------------------------------------
(* Graph 1: a simple cycle with no violations. *)
G1 == [states   |-> 1..3,
       initials |-> {1},
       actions  |-> << {2}, {3}, {1} >>]
V1 == {}
C1 == << >>

(* Graph 2: a linear chain whose last state violates. *)
G2 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {2}, {3}, {4}, {} >>]
V2 == {4}
C2 == << 1, 2, 3, 4 >>

(* Graph 3: two initial states, branching and a back edge. *)
G3 == [states   |-> 1..5,
       initials |-> {1, 2},
       actions  |-> << {3}, {3}, {4, 5}, {}, {1} >>]
V3 == {5}
C3 == << 1, 3, 5 >>

(* Graph 4: a diamond with a self-loop on the sink. No violations. *)
G4 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {2, 3}, {4}, {4}, {4} >>]
V4 == {}
C4 == << >>

(* Graph 5: a single state with a self-loop. The initial state violates. *)
G5 == [states   |-> 1..1,
       initials |-> {1},
       actions  |-> << {1} >>]
V5 == {1}
C5 == << 1 >>

(* Graph 6: two disconnected components. The violation is unreachable. *)
G6 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {2}, {1}, {4}, {3} >>]
V6 == {3}
C6 == << >>

(* Graph 7 (default): a branching DAG with a violating sink. *)
G7 == [states   |-> 1..6,
       initials |-> {1},
       actions  |-> << {2, 3}, {4}, {4, 5}, {6}, {6}, {} >>]
V7 == {6}
C7 == << 1, 2, 4, 6 >>

(* Graph 8: no initial states, so nothing is reachable. *)
G8 == [states   |-> 1..2,
       initials |-> {},
       actions  |-> << {2}, {1} >>]
V8 == {1}
C8 == << >>

-----------------------------------------------------------------------------
(* Choosing the test case from the IO environment. *)

GraphName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestGraph ==
    CASE GraphName = "1" -> G1
      [] GraphName = "2" -> G2
      [] GraphName = "3" -> G3
      [] GraphName = "4" -> G4
      [] GraphName = "5" -> G5
      [] GraphName = "6" -> G6
      [] GraphName = "8" -> G8
      [] OTHER           -> G7

TestViolations ==
    CASE GraphName = "1" -> V1
      [] GraphName = "2" -> V2
      [] GraphName = "3" -> V3
      [] GraphName = "4" -> V4
      [] GraphName = "5" -> V5
      [] GraphName = "6" -> V6
      [] GraphName = "8" -> V8
      [] OTHER           -> V7

TestCounterexample ==
    CASE GraphName = "1" -> C1
      [] GraphName = "2" -> C2
      [] GraphName = "3" -> C3
      [] GraphName = "4" -> C4
      [] GraphName = "5" -> C5
      [] GraphName = "6" -> C6
      [] GraphName = "8" -> C8
      [] OTHER           -> C7

-----------------------------------------------------------------------------
(* Checks that the selected test data is well formed. *)

IsWellFormedGraph(G) ==
    /\ G.initials \subseteq G.states
    /\ DOMAIN G.actions = G.states
    /\ \A s \in G.states : G.actions[s] \subseteq G.states

IsPath(G, p) ==
    /\ p # << >> => p[1] \in G.initials
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in G.actions[p[i]]

ASSUME IsWellFormedGraph(TestGraph)
ASSUME TestViolations \subseteq TestGraph.states
ASSUME IsPath(TestGraph, TestCounterexample)
ASSUME TestCounterexample # << >> =>
           TestCounterexample[Len(TestCounterexample)] \in TestViolations

=============================================================================