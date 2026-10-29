------------------------------ MODULE TestGraphs ------------------------------
(***************************************************************************)
(* A static library of directed state graphs, with violation sets and     *)
(* counterexample paths, for testing model-checker specifications such as *)
(* TLCMC and MCReachability.                                              *)
(*                                                                         *)
(* Each graph is a record with these fields:                              *)
(*   states   : the set of states (state numbers 1..N)                    *)
(*   initials : the set of initial states                                 *)
(*   actions  : a sequence of successor-state sets, indexed by state      *)
(*                                                                         *)
(* Vi is the set of violating states of graph Gi.                         *)
(* Wi is a witness path from an initial state to a violating state, or    *)
(* <<>> when no violating state is reachable.                             *)
(*                                                                         *)
(* The test case is chosen with the IO environment variable GRAPH. When   *)
(* GRAPH is not set, graph 7 is used.                                     *)
(*                                                                         *)
(* This module declares no variables, actions, temporal specification or  *)
(* fairness conditions.                                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, IOUtils

-----------------------------------------------------------------------------
(* Graph 1: a simple chain with a self loop. No violations. *)
G1 == [ states   |-> 1..3,
        initials |-> {1},
        actions  |-> << {1, 2}, {3}, {} >> ]
V1 == {}
W1 == << >>

(* Graph 2: a cycle in which the last state violates. *)
G2 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {3}, {4}, {1} >> ]
V2 == {4}
W2 == << 1, 2, 3, 4 >>

(* Graph 3: two initial states and a branching structure. *)
G3 == [ states   |-> 1..5,
        initials |-> {1, 3},
        actions  |-> << {2}, {2}, {4, 5}, {}, {1} >> ]
V3 == {5}
W3 == << 3, 5 >>

(* Graph 4: one state with a self loop. The initial state violates. *)
G4 == [ states   |-> 1..1,
        initials |-> {1},
        actions  |-> << {1} >> ]
V4 == {1}
W4 == << 1 >>

(* Graph 5: no initial states, so the violation is unreachable. *)
G5 == [ states   |-> 1..2,
        initials |-> {},
        actions  |-> << {2}, {1} >> ]
V5 == {2}
W5 == << >>

(* Graph 6: a diamond. No violations. *)
G6 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2, 3}, {4}, {4}, {} >> ]
V6 == {}
W6 == << >>

(* Graph 7 (the default): branches, joins, a back edge and a self loop. *)
G7 == [ states   |-> 1..6,
        initials |-> {1},
        actions  |-> << {2, 3}, {4}, {4, 5}, {6}, {1}, {6} >> ]
V7 == {6}
W7 == << 1, 2, 4, 6 >>

(* Graph 8: two separate components. The violation is unreachable. *)
G8 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {1}, {4}, {3} >> ]
V8 == {3}
W8 == << >>

-----------------------------------------------------------------------------
(* Choose the test case from the IO environment variable GRAPH. *)
(* Use graph 7 when GRAPH is not set.                           *)

GraphName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestCase ==
    CASE GraphName = "1" -> [ graph |-> G1, violations |-> V1, witness |-> W1 ]
      [] GraphName = "2" -> [ graph |-> G2, violations |-> V2, witness |-> W2 ]
      [] GraphName = "3" -> [ graph |-> G3, violations |-> V3, witness |-> W3 ]
      [] GraphName = "4" -> [ graph |-> G4, violations |-> V4, witness |-> W4 ]
      [] GraphName = "5" -> [ graph |-> G5, violations |-> V5, witness |-> W5 ]
      [] GraphName = "6" -> [ graph |-> G6, violations |-> V6, witness |-> W6 ]
      [] GraphName = "7" -> [ graph |-> G7, violations |-> V7, witness |-> W7 ]
      [] GraphName = "8" -> [ graph |-> G8, violations |-> V8, witness |-> W8 ]
      [] OTHER           -> [ graph |-> G7, violations |-> V7, witness |-> W7 ]

(* Accessors used by the specifications under test. *)
StateGraph      == TestCase.graph
ViolationStates == TestCase.violations
Counterexample  == TestCase.witness

(* Convenience views of the selected graph. *)
States        == StateGraph.states
InitialStates == StateGraph.initials
Successors(s) == StateGraph.actions[s]

=============================================================================