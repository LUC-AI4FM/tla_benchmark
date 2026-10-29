---------------------------- MODULE TestGraphs ----------------------------
(***************************************************************************)
(* A library of directed state graphs used as test cases for verifying     *)
(* model-checker implementations (reachability analysis and counterexample *)
(* generation).  Each graph is a record with fields:                       *)
(*   states          : finite set of states                                *)
(*   initials        : subset of states                                    *)
(*   actions         : function  state -> set of successor states          *)
(*   violations      : set of "bad" states                                 *)
(*   counterexamples : set of expected paths (sequences) from an initial   *)
(*                     state to a violation state                          *)
(* The graph under test is selected at runtime via the constant GraphName  *)
(* (which may be bound from an environment variable by the harness).      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT GraphName

VARIABLE state

vars == <<state>>

Min(a, b) == IF a < b THEN a ELSE b

(***************************************************************************)
(* Simple case: 1 -> 2 -> 3, violation at 3.                              *)
(***************************************************************************)
SimpleGraph ==
  [ states          |-> {1, 2, 3},
    initials        |-> {1},
    actions         |-> (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {}),
    violations      |-> {3},
    counterexamples |-> { <<1, 2, 3>> } ]

(***************************************************************************)
(* Unreachable violation: 1 <-> 2 cycle, violation 3 only self-reachable. *)
(***************************************************************************)
UnreachableGraph ==
  [ states          |-> {1, 2, 3},
    initials        |-> {1},
    actions         |-> (1 :> {2}) @@ (2 :> {1}) @@ (3 :> {3}),
    violations      |-> {3},
    counterexamples |-> {} ]

(***************************************************************************)
(* Multiple initial states.                                                *)
(***************************************************************************)
MultiInitGraph ==
  [ states          |-> {1, 2, 3, 4},
    initials        |-> {1, 3},
    actions         |-> (1 :> {2}) @@ (2 :> {}) @@ (3 :> {4}) @@ (4 :> {}),
    violations      |-> {4},
    counterexamples |-> { <<3, 4>> } ]

(***************************************************************************)
(* Forest with a disconnected, unreachable component.                      *)
(***************************************************************************)
ForestGraph ==
  [ states          |-> {1, 2, 3, 4, 5, 6},
    initials        |-> {1},
    actions         |-> (1 :> {2, 3}) @@ (2 :> {}) @@ (3 :> {}) @@
                        (4 :> {5, 6}) @@ (5 :> {}) @@ (6 :> {}),
    violations      |-> {3, 6},
    counterexamples |-> { <<1, 3>> } ]

(***************************************************************************)
(* Cycle / strongly connected component with an exit to a violation.       *)
(***************************************************************************)
CycleGraph ==
  [ states          |-> {1, 2, 3, 4},
    initials        |-> {1},
    actions         |-> (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {1, 4}) @@ (4 :> {4}),
    violations      |-> {4},
    counterexamples |-> { <<1, 2, 3, 4>> } ]

(***************************************************************************)
(* Multiple distinct paths to the violation.                               *)
(***************************************************************************)
MultiPathGraph ==
  [ states          |-> {1, 2, 3, 4, 5},
    initials        |-> {1},
    actions         |-> (1 :> {2, 3}) @@ (2 :> {4}) @@ (3 :> {4}) @@
                        (4 :> {5}) @@ (5 :> {}),
    violations      |-> {5},
    counterexamples |-> { <<1, 2, 4, 5>>, <<1, 3, 4, 5>> } ]

(***************************************************************************)
(* Edge cases.                                                             *)
(***************************************************************************)
EmptyGraph ==
  [ states          |-> {},
    initials        |-> {},
    actions         |-> [s \in {} |-> {}],
    violations      |-> {},
    counterexamples |-> {} ]

SingleNodeGraph ==
  [ states          |-> {1},
    initials        |-> {1},
    actions         |-> (1 :> {1}),
    violations      |-> {1},
    counterexamples |-> { <<1>> } ]

NoInitGraph ==
  [ states          |-> {1, 2},
    initials        |-> {},
    actions         |-> (1 :> {2}) @@ (2 :> {}),
    violations      |-> {2},
    counterexamples |-> {} ]

NoViolationGraph ==
  [ states          |-> {1, 2, 3},
    initials        |-> {1},
    actions         |-> (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {1}),
    violations      |-> {},
    counterexamples |-> {} ]

(***************************************************************************)
(* Larger realistic example: water-jug puzzle with a 4-gallon and a        *)
(* 9-gallon jug (50 states).  Violation: big jug holds exactly 6 gallons.  *)
(***************************************************************************)
SmallCap == 4
BigCap   == 9

JugStates == { <<s, b>> : s \in 0..SmallCap, b \in 0..BigCap }

JugSucc(st) ==
  LET s == st[1]
      b == st[2]
      toBig   == Min(s, BigCap - b)
      toSmall == Min(b, SmallCap - s)
  IN { <<SmallCap, b>>,              \* fill small
       <<s, BigCap>>,                \* fill big
       <<0, b>>,                     \* empty small
       <<s, 0>>,                     \* empty big
       <<s - toBig, b + toBig>>,     \* pour small into big
       <<s + toSmall, b - toSmall>>  \* pour big into small
     }

WaterJugGraph ==
  [ states          |-> JugStates,
    initials        |-> { <<0, 0>> },
    actions         |-> [st \in JugStates |-> JugSucc(st)],
    violations      |-> { st \in JugStates : st[2] = 6 },
    counterexamples |->
      { << <<0, 0>>, <<0, 9>>, <<4, 5>>, <<0, 5>>, <<4, 1>>,
           <<0, 1>>, <<1, 0>>, <<1, 9>>, <<4, 6>> >> } ]

(***************************************************************************)
(* The library of test graphs, indexed by name.                            *)
(***************************************************************************)
Graphs ==
     ("simple"       :> SimpleGraph)
  @@ ("unreachable"  :> UnreachableGraph)
  @@ ("multiinit"    :> MultiInitGraph)
  @@ ("forest"       :> ForestGraph)
  @@ ("cycle"        :> CycleGraph)
  @@ ("multipath"    :> MultiPathGraph)
  @@ ("empty"        :> EmptyGraph)
  @@ ("singlenode"   :> SingleNodeGraph)
  @@ ("noinit"       :> NoInitGraph)
  @@ ("noviolation"  :> NoViolationGraph)
  @@ ("waterjug"     :> WaterJugGraph)

(***************************************************************************)
(* Reachability and well-formedness of test data.                          *)
(***************************************************************************)
RECURSIVE ReachFrom(_, _)
ReachFrom(g, S) ==
  LET N == S \cup UNION { g.actions[s] : s \in S }
  IN  IF N = S THEN S ELSE ReachFrom(g, N)

Reachable(g) == ReachFrom(g, g.initials)

ViolationReachable(g) == Reachable(g) \cap g.violations # {}

IsCounterexample(g, p) ==
  /\ Len(p) >= 1
  /\ p[1] \in g.initials
  /\ \A i \in 1..Len(p) : p[i] \in g.states
  /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in g.actions[p[i]]
  /\ p[Len(p)] \in g.violations

WellFormed(g) ==
  /\ g.initials \subseteq g.states
  /\ DOMAIN g.actions = g.states
  /\ \A s \in g.states : g.actions[s] \subseteq g.states
  /\ g.violations \subseteq g.states
  \* Property 1: every expected counterexample is a valid path
  /\ \A p \in g.counterexamples : IsCounterexample(g, p)
  \* Properties 1 & 2: counterexamples exist iff a violation is reachable
  /\ (g.counterexamples = {}) <=> ~ViolationReachable(g)

ASSUME GraphName \in DOMAIN Graphs
ASSUME \A n \in DOMAIN Graphs : WellFormed(Graphs[n])

(***************************************************************************)
(* Behavior: explore the selected graph.                                   *)
(***************************************************************************)
G == Graphs[GraphName]

Init == state \in G.initials

Next == \E t \in G.actions[state] : state' = t

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeOK == state \in G.states

StateReachable == state \in Reachable(G)

\* The invariant a model checker under test should check; it is violated
\* exactly when G.counterexamples is non-empty.
NoViolation == state \notin G.violations

=============================================================================