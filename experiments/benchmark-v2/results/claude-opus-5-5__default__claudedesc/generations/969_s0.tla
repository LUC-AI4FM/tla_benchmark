------------------------------ MODULE TestGraphs ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* A library of directed state graphs used as test fixtures for TLCMC and  *)
(* MCReachability.  Each graph is a record with fields:                     *)
(*   states   : the set of states (integer ranges)                          *)
(*   initials : the set of initial states                                   *)
(*   actions  : a sequence; actions[i] is the set of successors of state i  *)
(* For each graph Gx there is a violation set Vx and a set CXx of expected  *)
(* (shortest) counterexample traces reaching a violating state.            *)
(*                                                                         *)
(* GRAPH plays the role of the environment variable GRAPH; any value not   *)
(* naming a known graph selects graph seven by default.                    *)
(***************************************************************************)
CONSTANT GRAPH

VARIABLE state

Min(a, b) == IF a < b THEN a ELSE b

-----------------------------------------------------------------------------
(* G1: a simple cycle *)
G1 == [states |-> 1..4, initials |-> {1},
       actions |-> << {2}, {3}, {4}, {1} >>]
V1 == {3}
CX1 == { <<1, 2, 3>> }

(* G2: multiple initial states *)
G2 == [states |-> 1..4, initials |-> {1, 3},
       actions |-> << {2}, {4}, {4}, {} >>]
V2 == {4}
CX2 == { <<3, 4>> }

(* G3: disconnected components; the violation is unreachable *)
G3 == [states |-> 1..5, initials |-> {1},
       actions |-> << {2}, {1}, {4}, {5}, {3} >>]
V3 == {4}
CX3 == {}

(* G4: strongly connected components *)
G4 == [states |-> 1..5, initials |-> {1},
       actions |-> << {2}, {3}, {1, 4}, {5}, {4} >>]
V4 == {5}
CX4 == { <<1, 2, 3, 4, 5>> }

(* G5: two initial states converging *)
G5 == [states |-> 1..4, initials |-> {1, 2},
       actions |-> << {3}, {3}, {4}, {1} >>]
V5 == {4}
CX5 == { <<1, 3, 4>>, <<2, 3, 4>> }

(* G6: diamond shape, two shortest paths *)
G6 == [states |-> 1..5, initials |-> {1},
       actions |-> << {2, 3}, {4}, {4}, {5}, {} >>]
V6 == {5}
CX6 == { <<1, 2, 4, 5>>, <<1, 3, 4, 5>> }

(* G7: medium-sized graph with fifty states; forward chain plus back edges *)
G7 == [states |-> 1..50, initials |-> {1},
       actions |-> [i \in 1..50 |->
                      IF i < 50 THEN {i + 1, (i \div 2) + 1} ELSE {1}]]
V7 == {50}
CX7 == { [i \in 1..50 |-> i] }

(* G8: self-loops *)
G8 == [states |-> 1..3, initials |-> {1},
       actions |-> << {1, 2}, {2, 3}, {3} >>]
V8 == {3}
CX8 == { <<1, 2, 3>> }

(* G9: the empty graph *)
G9 == [states |-> {}, initials |-> {},
       actions |-> << >>]
V9 == {}
CX9 == {}

(* G10: no initial states *)
G10 == [states |-> 1..3, initials |-> {},
        actions |-> << {2}, {3}, {1} >>]
V10 == {2}
CX10 == {}

(* G11: simple linear sequence *)
G11 == [states |-> 1..3, initials |-> {1},
        actions |-> << {2}, {3}, {} >>]
V11 == {3}
CX11 == { <<1, 2, 3>> }

(* G12: single state with self-loop, initial state is a violation *)
G12 == [states |-> {1}, initials |-> {1},
        actions |-> << {1} >>]
V12 == {1}
CX12 == { <<1>> }

(* G13: linear sequence without violations *)
G13 == [states |-> 1..5, initials |-> {1},
        actions |-> << {2}, {3}, {4}, {5}, {} >>]
V13 == {}
CX13 == {}

-----------------------------------------------------------------------------
(* GDH: state space of the DieHard puzzle (3 and 5 gallon jugs).          *)
(* Jug state (s, b) is encoded as index 1 + 25*s + b; indices that do not  *)
(* encode a valid jug state have no successors.                            *)
DHIdx(s, b) == 1 + 25 * s + b
DHSmall(i) == (i - 1) \div 25
DHBig(i) == (i - 1) % 25
DHValid(i) == DHSmall(i) <= 3 /\ DHBig(i) <= 5

DHNext(s, b) ==
  LET p == Min(s, 5 - b)   \* pour small into big
      q == Min(b, 3 - s)   \* pour big into small
  IN { DHIdx(3, b), DHIdx(s, 5), DHIdx(0, b), DHIdx(s, 0),
       DHIdx(s - p, b + p), DHIdx(s + q, b - q) }

GDH == [states |-> 1..101, initials |-> {DHIdx(0, 0)},
        actions |-> [i \in 1..101 |->
                       IF DHValid(i) THEN DHNext(DHSmall(i), DHBig(i))
                                     ELSE {}]]
VDH == { DHIdx(s, 4) : s \in 0..3 }
CXDH == { << DHIdx(0, 0), DHIdx(0, 5), DHIdx(3, 2), DHIdx(0, 2),
             DHIdx(2, 0), DHIdx(2, 5), DHIdx(3, 4) >> }

-----------------------------------------------------------------------------
(* Selection of the test case via GRAPH, defaulting to graph seven. *)
TestCase ==
  CASE GRAPH = "1"  -> G1
    [] GRAPH = "2"  -> G2
    [] GRAPH = "3"  -> G3
    [] GRAPH = "4"  -> G4
    [] GRAPH = "5"  -> G5
    [] GRAPH = "6"  -> G6
    [] GRAPH = "7"  -> G7
    [] GRAPH = "8"  -> G8
    [] GRAPH = "9"  -> G9
    [] GRAPH = "10" -> G10
    [] GRAPH = "11" -> G11
    [] GRAPH = "12" -> G12
    [] GRAPH = "13" -> G13
    [] GRAPH = "DH" -> GDH
    [] OTHER        -> G7

TestViolations ==
  CASE GRAPH = "1"  -> V1
    [] GRAPH = "2"  -> V2
    [] GRAPH = "3"  -> V3
    [] GRAPH = "4"  -> V4
    [] GRAPH = "5"  -> V5
    [] GRAPH = "6"  -> V6
    [] GRAPH = "7"  -> V7
    [] GRAPH = "8"  -> V8
    [] GRAPH = "9"  -> V9
    [] GRAPH = "10" -> V10
    [] GRAPH = "11" -> V11
    [] GRAPH = "12" -> V12
    [] GRAPH = "13" -> V13
    [] GRAPH = "DH" -> VDH
    [] OTHER        -> V7

TestCounterexamples ==
  CASE GRAPH = "1"  -> CX1
    [] GRAPH = "2"  -> CX2
    [] GRAPH = "3"  -> CX3
    [] GRAPH = "4"  -> CX4
    [] GRAPH = "5"  -> CX5
    [] GRAPH = "6"  -> CX6
    [] GRAPH = "7"  -> CX7
    [] GRAPH = "8"  -> CX8
    [] GRAPH = "9"  -> CX9
    [] GRAPH = "10" -> CX10
    [] GRAPH = "11" -> CX11
    [] GRAPH = "12" -> CX12
    [] GRAPH = "13" -> CX13
    [] GRAPH = "DH" -> CXDH
    [] OTHER        -> CX7

-----------------------------------------------------------------------------
(* Well-formedness of a graph record *)
WellFormed(G) ==
  /\ G.initials \subseteq G.states
  /\ DOMAIN G.actions = G.states
  /\ \A i \in G.states : G.actions[i] \subseteq G.states

(* A behavior walks the selected graph. *)
Init == state \in TestCase.initials

Next == state' \in TestCase.actions[state]

Spec == Init /\ [][Next]_state

TypeOK == state \in TestCase.states

GraphOK == WellFormed(TestCase)

(* Every expected counterexample is a genuine path ending in a violation. *)
CounterexamplesOK ==
  \A cx \in TestCounterexamples :
    /\ Len(cx) > 0
    /\ cx[1] \in TestCase.initials
    /\ cx[Len(cx)] \in TestViolations
    /\ \A k \in 1..(Len(cx) - 1) : cx[k + 1] \in TestCase.actions[cx[k]]

(* The safety property whose violation the model checkers should report. *)
NoViolation == state \notin TestViolations
=============================================================================