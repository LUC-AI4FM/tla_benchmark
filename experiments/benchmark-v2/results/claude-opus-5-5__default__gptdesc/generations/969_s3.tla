---------------------------- MODULE TestGraphs ----------------------------
(***************************************************************************)
(* A static library of directed state graphs used to test model-checker   *)
(* specifications such as TLCMC and MCReachability.                       *)
(*                                                                         *)
(* Each graph is a record with fields:                                     *)
(*   states   - the set of states (numbered 1..N)                          *)
(*   initials - the set of initial states                                  *)
(*   actions  - a sequence whose i-th element is the set of successor      *)
(*              states of state i                                          *)
(*                                                                         *)
(* For every graph Gi there is a set Vi of violating states and a         *)
(* sequence Ci, an example counterexample path from an initial state to a *)
(* violating state. Ci is the empty sequence if no violating state can be *)
(* reached.                                                                *)
(*                                                                         *)
(* The test case is chosen with the IO environment variable GRAPH. If it  *)
(* is not set, graph 7 is used.                                            *)
(*                                                                         *)
(* The module has no variables, actions, temporal specification, fairness *)
(* or proofs.                                                              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, IOUtils

-----------------------------------------------------------------------------
(* Graph 1: A simple cycle with no violations. *)
G1 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {3}, {4}, {1} >> ]
V1 == {}
C1 == << >>

(* Graph 2: A linear chain that ends in a violating deadlock state. *)
G2 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {3}, {4}, {} >> ]
V2 == {4}
C2 == << 1, 2, 3, 4 >>

(* Graph 3: An initial state is itself a violation. *)
G3 == [ states   |-> 1..3,
        initials |-> {1, 3},
        actions  |-> << {1, 2}, {3}, {} >> ]
V3 == {3}
C3 == << 3 >>

(* Graph 4: A diamond in which two paths reach the violation. *)
G4 == [ states   |-> 1..5,
        initials |-> {1},
        actions  |-> << {2, 3}, {4}, {4}, {5}, {5} >> ]
V4 == {5}
C4 == << 1, 2, 4, 5 >>

(* Graph 5: The empty graph. *)
G5 == [ states   |-> {},
        initials |-> {},
        actions  |-> << >> ]
V5 == {}
C5 == << >>

(* Graph 6: A single state with a self-loop. *)
G6 == [ states   |-> {1},
        initials |-> {1},
        actions  |-> << {1} >> ]
V6 == {}
C6 == << >>

(* Graph 7 (default): Several initial states, cycles, and a reachable     *)
(* violation that has a self-loop.                                        *)
G7 == [ states   |-> 1..6,
        initials |-> {1, 2},
        actions  |-> << {3}, {4}, {5}, {5, 6}, {1}, {6} >> ]
V7 == {6}
C7 == << 2, 4, 6 >>

(* Graph 8: The violating state cannot be reached. *)
G8 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {1}, {4}, {3} >> ]
V8 == {4}
C8 == << >>

-----------------------------------------------------------------------------
(* Choose the test case from the IO environment variable GRAPH. *)

GraphName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestCase ==
    CASE GraphName = "1" -> [ graph |-> G1, violations |-> V1, counterexample |-> C1 ]
      [] GraphName = "2" -> [ graph |-> G2, violations |-> V2, counterexample |-> C2 ]
      [] GraphName = "3" -> [ graph |-> G3, violations |-> V3, counterexample |-> C3 ]
      [] GraphName = "4" -> [ graph |-> G4, violations |-> V4, counterexample |-> C4 ]
      [] GraphName = "5" -> [ graph |-> G5, violations |-> V5, counterexample |-> C5 ]
      [] GraphName = "6" -> [ graph |-> G6, violations |-> V6, counterexample |-> C6 ]
      [] GraphName = "8" -> [ graph |-> G8, violations |-> V8, counterexample |-> C8 ]
      [] OTHER           -> [ graph |-> G7, violations |-> V7, counterexample |-> C7 ]

TestGraph          == TestCase.graph
TestViolations     == TestCase.violations
TestCounterexample == TestCase.counterexample

(* Helpers for test specifications that use the selected graph. *)
StateSet     == TestGraph.states
InitialSet   == TestGraph.initials
Successors(s) == TestGraph.actions[s]

=============================================================================