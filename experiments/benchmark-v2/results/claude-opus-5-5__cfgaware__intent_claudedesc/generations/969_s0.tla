---------------------------- MODULE TestGraphs ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* A library of directed state graphs used to test model checkers.         *)
(* Each graph is a record with fields:                                     *)
(*   states   : the finite set of states                                   *)
(*   initials : the subset of initial states                               *)
(*   actions  : a function mapping each state to its set of successors     *)
(*   inv      : the set of violation ("bad") states                        *)
(*   cexs     : a set of expected counterexample paths (sequences)         *)
(***************************************************************************)

MkGraph(S, I, A, V, C) ==
    [states |-> S, initials |-> I, actions |-> A, inv |-> V, cexs |-> C]

\* Simple: 1 -> 2 -> 3, violation 3
G1 == MkGraph({1, 2, 3}, {1},
              (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {}),
              {3},
              {<<1, 2, 3>>})

\* Unreachable violation: 1 -> 2, 3 isolated and bad
G2 == MkGraph({1, 2, 3}, {1},
              (1 :> {2}) @@ (2 :> {1}) @@ (3 :> {3}),
              {3},
              {})

\* Multiple initial states
G3 == MkGraph({1, 2, 3, 4}, {1, 2},
              (1 :> {3}) @@ (2 :> {4}) @@ (3 :> {3}) @@ (4 :> {4}),
              {4},
              {<<2, 4>>})

\* Forest: two disconnected components, violation in unreachable tree
G4 == MkGraph({1, 2, 3, 4, 5, 6}, {1},
              (1 :> {2, 3}) @@ (2 :> {}) @@ (3 :> {}) @@
              (4 :> {5, 6}) @@ (5 :> {}) @@ (6 :> {}),
              {6},
              {})

\* Cycle / SCC with exit to violation
G5 == MkGraph({1, 2, 3, 4}, {1},
              (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {1, 4}) @@ (4 :> {4}),
              {4},
              {<<1, 2, 3, 4>>})

\* Multiple paths to violations (diamond with two bad states)
G6 == MkGraph({1, 2, 3, 4, 5}, {1},
              (1 :> {2, 3}) @@ (2 :> {4}) @@ (3 :> {4, 5}) @@
              (4 :> {}) @@ (5 :> {}),
              {4, 5},
              {<<1, 2, 4>>, <<1, 3, 4>>, <<1, 3, 5>>})

\* Empty graph
G7 == MkGraph({}, {}, [s \in {} |-> {}], {}, {})

\* Single node, self loop, no violation
G8 == MkGraph({1}, {1}, (1 :> {1}), {}, {})

\* Single node that is itself a violation
G9 == MkGraph({1}, {1}, (1 :> {}), {1}, {<<1>>})

\* No initial states
G10 == MkGraph({1, 2}, {},
               (1 :> {2}) @@ (2 :> {1}),
               {2},
               {})

\* No violations, with cycles
G11 == MkGraph({1, 2, 3}, {1},
               (1 :> {2}) @@ (2 :> {3}) @@ (3 :> {1}),
               {},
               {})

\* Larger graph (64 states): from n go to n+1 and 2n (when in range).
LStates == 0..63
G12 == MkGraph(LStates, {1},
               [n \in LStates |->
                   {m \in LStates : m = n + 1 \/ m = 2 * n}],
               {63},
               {<<1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63>>})

TestGraphs ==
    ("Simple"        :> G1)  @@ ("Unreachable"  :> G2)  @@
    ("MultiInit"     :> G3)  @@ ("Forest"       :> G4)  @@
    ("Cycle"         :> G5)  @@ ("MultiPath"    :> G6)  @@
    ("Empty"         :> G7)  @@ ("SingleNode"   :> G8)  @@
    ("SingleBad"     :> G9)  @@ ("NoInit"       :> G10) @@
    ("NoViolation"   :> G11) @@ ("Large"        :> G12)

\* Selected test case (can be overridden by the configuration).
TestCase == TestGraphs["Simple"]

(***************************************************************************)
(* Well-formedness of a test graph.                                        *)
(***************************************************************************)
IsPath(G, p) ==
    /\ Len(p) >= 1
    /\ \A i \in 1..Len(p) : p[i] \in G.states
    /\ p[1] \in G.initials
    /\ p[Len(p)] \in G.inv
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in G.actions[p[i]]

WellFormed(G) ==
    /\ G.initials \subseteq G.states
    /\ G.inv \subseteq G.states
    /\ DOMAIN G.actions = G.states
    /\ \A s \in G.states : G.actions[s] \subseteq G.states
    /\ \A p \in G.cexs : IsPath(G, p)

ASSUME \A g \in DOMAIN TestGraphs : WellFormed(TestGraphs[g])

(***************************************************************************)
(* A behavior spec walking the selected graph.                             *)
(***************************************************************************)
VARIABLE state

Init == state \in TestCase.initials

Next == state' \in TestCase.actions[state]

Spec == Init /\ [][Next]_state

Inv == state \notin TestCase.inv

=============================================================================