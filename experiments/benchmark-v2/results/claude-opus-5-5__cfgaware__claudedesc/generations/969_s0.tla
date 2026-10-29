----------------------------- MODULE TestGraphs -----------------------------
(***************************************************************************)
(* A library of directed state graphs used as test fixtures for the        *)
(* TLCMC and MCReachability specifications.                                *)
(*                                                                         *)
(* Each graph is a record with three fields:                               *)
(*   states   : the set of states (usually an integer range),              *)
(*   initials : the set of initial states,                                 *)
(*   actions  : a sequence; actions[i] is the set of successors of i.      *)
(*                                                                         *)
(* Each graph Gx has a violation set Vx and a counterexample set CXx.      *)
(* CXx holds the expected error traces that reach the violation states.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, IOUtils

-----------------------------------------------------------------------------
(* G1: a simple cycle 1 -> 2 -> 3 -> 4 -> 1 *)
G1 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {2}, {3}, {4}, {1} >>]
V1 == {4}
CX1 == { <<1, 2, 3, 4>> }

(* G2: multiple initial states *)
G2 == [states   |-> 1..4,
       initials |-> {1, 3},
       actions  |-> << {2}, {4}, {4}, {} >>]
V2 == {4}
CX2 == { <<1, 2, 4>>, <<3, 4>> }

(* G3: disconnected components; violation unreachable *)
G3 == [states   |-> 1..5,
       initials |-> {1},
       actions  |-> << {2}, {1}, {4}, {5}, {3} >>]
V3 == {4}
CX3 == {}

(* G4: strongly connected component plus a sink; no violations *)
G4 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {2}, {3}, {1, 4}, {4} >>]
V4 == {}
CX4 == {}

(* G5: two initial states feeding into a strongly connected component *)
G5 == [states   |-> 1..5,
       initials |-> {1, 2},
       actions  |-> << {3}, {3}, {4, 5}, {3}, {5} >>]
V5 == {5}
CX5 == { <<1, 3, 5>>, <<2, 3, 5>> }

(* G6: initial state outside of a cycle *)
G6 == [states   |-> 1..4,
       initials |-> {4},
       actions  |-> << {2}, {3}, {1}, {1} >>]
V6 == {3}
CX6 == { <<4, 1, 2, 3>> }

(* G7: medium-sized graph with fifty states, forward edges and back edges *)
G7 == [states   |-> 1..50,
       initials |-> {1},
       actions  |-> [i \in 1..50 |->
                        IF i < 50 THEN {i + 1, (i \div 2) + 1}
                                  ELSE {1}]]
V7 == {50}
CX7 == { [i \in 1..50 |-> i] }

(* G8: self-loops on every state *)
G8 == [states   |-> 1..4,
       initials |-> {1},
       actions  |-> << {1, 2}, {2, 3}, {3, 4}, {4} >>]
V8 == {4}
CX8 == { <<1, 2, 3, 4>> }

(* G9: the empty graph *)
G9 == [states   |-> {},
       initials |-> {},
       actions  |-> << >>]
V9 == {}
CX9 == {}

(* G10: no initial states *)
G10 == [states   |-> 1..3,
        initials |-> {},
        actions  |-> << {2}, {3}, {1} >>]
V10 == {1}
CX10 == {}

(* G11: a single state that is itself a violation *)
G11 == [states   |-> 1..1,
        initials |-> {1},
        actions  |-> << {} >>]
V11 == {1}
CX11 == { <<1>> }

(* G12: simple linear sequence of two states *)
G12 == [states   |-> 1..2,
        initials |-> {1},
        actions  |-> << {2}, {} >>]
V12 == {2}
CX12 == { <<1, 2>> }

(* G13: simple linear sequence of three states, no violations *)
G13 == [states   |-> 1..3,
        initials |-> {1},
        actions  |-> << {2}, {3}, {} >>]
V13 == {}
CX13 == {}

-----------------------------------------------------------------------------
(* GDH: the state space of the DieHard puzzle.  A state (big, small),      *)
(* with big \in 0..5 and small \in 0..3, is encoded as 1 + 10*big + small. *)
(* The graph has 101 states; indices that do not encode a jug              *)
(* configuration have no successors.                                       *)

Enc(b, s) == 1 + 10 * b + s

Min(a, b) == IF a < b THEN a ELSE b

IsEnc(i) == \E b \in 0..5, s \in 0..3 : Enc(b, s) = i

Big(i)   == (i - 1) \div 10
Small(i) == (i - 1) % 10

DHSucc(b, s) ==
    { Enc(5, s), Enc(b, 3), Enc(0, s), Enc(b, 0),
      Enc(b - Min(b, 3 - s), s + Min(b, 3 - s)),
      Enc(b + Min(s, 5 - b), s - Min(s, 5 - b)) }

GDH == [states   |-> 1..101,
        initials |-> {Enc(0, 0)},
        actions  |-> [i \in 1..101 |->
                        IF IsEnc(i) THEN DHSucc(Big(i), Small(i))
                                    ELSE {}]]
VDH == { Enc(4, s) : s \in 0..3 }
(* (0,0) -> (5,0) -> (2,3) -> (2,0) -> (0,2) -> (5,2) -> (4,3) *)
CXDH == { << Enc(0,0), Enc(5,0), Enc(2,3), Enc(2,0),
             Enc(0,2), Enc(5,2), Enc(4,3) >> }

-----------------------------------------------------------------------------
Mk(g, v, cx) == [states          |-> g.states,
                 initials        |-> g.initials,
                 actions         |-> g.actions,
                 violations      |-> v,
                 counterexamples |-> cx]

GraphName == IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestCase ==
    CASE GraphName = "1"  -> Mk(G1, V1, CX1)
      [] GraphName = "2"  -> Mk(G2, V2, CX2)
      [] GraphName = "3"  -> Mk(G3, V3, CX3)
      [] GraphName = "4"  -> Mk(G4, V4, CX4)
      [] GraphName = "5"  -> Mk(G5, V5, CX5)
      [] GraphName = "6"  -> Mk(G6, V6, CX6)
      [] GraphName = "7"  -> Mk(G7, V7, CX7)
      [] GraphName = "8"  -> Mk(G8, V8, CX8)
      [] GraphName = "9"  -> Mk(G9, V9, CX9)
      [] GraphName = "10" -> Mk(G10, V10, CX10)
      [] GraphName = "11" -> Mk(G11, V11, CX11)
      [] GraphName = "12" -> Mk(G12, V12, CX12)
      [] GraphName = "13" -> Mk(G13, V13, CX13)
      [] GraphName = "DH" -> Mk(GDH, VDH, CXDH)
      [] OTHER            -> Mk(G7, V7, CX7)

=============================================================================