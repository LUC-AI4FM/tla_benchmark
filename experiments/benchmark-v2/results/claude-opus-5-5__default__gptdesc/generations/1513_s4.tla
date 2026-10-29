---------------------------- MODULE TerminationStateMachine ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. N-1
Color == {"white", "black"}

-----------------------------------------------------------------------------
(* Type constraints *)

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color  \in [Nodes -> Color]
  /\ tpos   \in Nodes
  /\ tcolor \in Color

-----------------------------------------------------------------------------
(* Auxiliary predicates used as constraints on states *)

terminated == \A i \in Nodes : ~ active[i]

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

(* Structural constraint relating the token to node states, in the style of
   the Dijkstra-Feijen-van Gasteren termination detection invariant. *)
Constraint ==
  \/ \A i \in Nodes : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

-----------------------------------------------------------------------------
(* Initial states: chosen nondeterministically subject to constraints *)

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color  \in [Nodes -> Color]
  /\ tpos   \in Nodes
  /\ tcolor \in Color
  /\ tpos = 0
  /\ tcolor = "black"

(* Next-state relation: chooses a successor state nondeterministically,
   subject to the constraints holding in the successor state. *)
Next ==
  /\ active' \in [Nodes -> BOOLEAN]
  /\ color'  \in [Nodes -> Color]
  /\ tpos'   \in Nodes
  /\ tcolor' \in Color
  /\ Constraint'
  /\ terminationDetected' => terminated'

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeInvariant == TypeOK

=============================================================================