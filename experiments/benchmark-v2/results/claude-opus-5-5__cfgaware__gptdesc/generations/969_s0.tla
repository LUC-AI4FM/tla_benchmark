---------------------------- MODULE TestGraphs ----------------------------
(***************************************************************************)
(* A static library of directed state graphs used to test model-checker  *)
(* specifications such as TLCMC and MCReachability.                       *)
(*                                                                         *)
(* Each graph is a record with fields:                                     *)
(*   states   : the set of states, numbered 1..N                           *)
(*   initials : the set of initial states                                  *)
(*   actions  : a sequence of successor-state sets, indexed by state      *)
(*                                                                         *)
(* For each graph Gi there is a set Vi of violating states and a           *)
(* counterexample path Ci, which is a path from an initial state to a      *)
(* violating state, or <<>> when no violating state is reachable.          *)
(*                                                                         *)
(* The test case is chosen with the environment variable GRAPH. If GRAPH   *)
(* is not set, graph 7 is used.                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC, IOUtils

-----------------------------------------------------------------------------
(* Graph 1: a simple chain with no violations. *)
G1 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {3}, {4}, {} >> ]
V1 == {}
C1 == << >>

(* Graph 2: a chain with a self-loop and a reachable violation. *)
G2 == [ states   |-> 1..3,
        initials |-> {1},
        actions  |-> << {1, 2}, {3}, {3} >> ]
V2 == {3}
C2 == << 1, 2, 3 >>

(* Graph 3: one state with a self-loop and no violations. *)
G3 == [ states   |-> 1..1,
        initials |-> {1},
        actions  |-> << {1} >> ]
V3 == {}
C3 == << >>

(* Graph 4: two initial states and a reachable violation. *)
G4 == [ states   |-> 1..5,
        initials |-> {1, 2},
        actions  |-> << {3}, {4}, {5}, {5}, {} >> ]
V4 == {4}
C4 == << 2, 4 >>

(* Graph 5: the violating state cannot be reached. *)
G5 == [ states   |-> 1..4,
        initials |-> {1},
        actions  |-> << {2}, {1}, {4}, {} >> ]
V5 == {3}
C5 == << >>

(* Graph 6: the initial state is itself a violation. *)
G6 == [ states   |-> 1..2,
        initials |-> {1},
        actions  |-> << {2}, {} >> ]
V6 == {1}
C6 == << 1 >>

(* Graph 7: a larger graph with a cycle and a deep violation. *)
G7 == [ states   |-> 1..8,
        initials |-> {1, 2},
        actions  |-> << {3, 4}, {4}, {5}, {6}, {7}, {8}, {1}, {} >> ]
V7 == {8}
C7 == << 1, 4, 6, 8 >>

(* Graph 8: no initial states, so nothing is reachable. *)
G8 == [ states   |-> 1..3,
        initials |-> {},
        actions  |-> << {2}, {3}, {} >> ]
V8 == {}
C8 == << >>

-----------------------------------------------------------------------------
(* Build a test-case record from a graph, its violations and a path. *)
MkTest(g, v, c) ==
    [ states         |-> g.states,
      initials       |-> g.initials,
      actions        |-> g.actions,
      violations     |-> v,
      counterexample |-> c ]

(* The selected graph name. Defaults to "7" when GRAPH is not set. *)
GraphName ==
    IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestCase ==
    CASE GraphName = "1" -> MkTest(G1, V1, C1)
      [] GraphName = "2" -> MkTest(G2, V2, C2)
      [] GraphName = "3" -> MkTest(G3, V3, C3)
      [] GraphName = "4" -> MkTest(G4, V4, C4)
      [] GraphName = "5" -> MkTest(G5, V5, C5)
      [] GraphName = "6" -> MkTest(G6, V6, C6)
      [] GraphName = "8" -> MkTest(G8, V8, C8)
      [] OTHER           -> MkTest(G7, V7, C7)

=============================================================================