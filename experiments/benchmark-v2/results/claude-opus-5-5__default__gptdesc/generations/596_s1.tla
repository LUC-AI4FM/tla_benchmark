---------------------------- MODULE CounterExampleSpec ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, TLCExt

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* Initial condition and transition relation                               *)
-----------------------------------------------------------------------------

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' \in {1, 2}
    \/ /\ x # 0
       /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

-----------------------------------------------------------------------------
(* Safety                                                                  *)
-----------------------------------------------------------------------------

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* Temporal properties                                                     *)
-----------------------------------------------------------------------------

\* Eventually x stabilizes away from 1, or away from 2.
\* This is violated by the behavior 0 -> 1 -> 0 -> 2 -> 0 -> ...
Stabilize == <>[](x # 1) \/ <>[](x # 2)

\* x returns to 0 infinitely often (holds under WF_x(Next)).
RepeatedlyZero == []<>(x = 0)

\* The negation of the stabilization property.
NotStabilize == ~Stabilize

-----------------------------------------------------------------------------
(* Postcondition: check the TLC-generated counterexample for Stabilize.    *)
(* TLC encodes the counterexample as a record with a set of indexed states *)
(* (tuples <<i, state>>) and a set of actions (tuples <<s, action, t>>).   *)
-----------------------------------------------------------------------------

ExpectedStates ==
    { <<1, [x |-> 0]>>,
      <<2, [x |-> 1]>>,
      <<3, [x |-> 0]>>,
      <<4, [x |-> 2]>> }

ExpectedEdges ==
    { << <<1, [x |-> 0]>>, <<2, [x |-> 1]>> >>,
      << <<2, [x |-> 1]>>, <<3, [x |-> 0]>> >>,
      << <<3, [x |-> 0]>>, <<4, [x |-> 2]>> >>,
      << <<4, [x |-> 2]>>, <<1, [x |-> 0]>> >> }

ActualEdges ==
    { <<a[1], a[3]>> : a \in CounterExample.action }

PostCondition ==
    /\ CounterExample.state = ExpectedStates
    /\ ActualEdges = ExpectedEdges
    /\ Cardinality(CounterExample.action) = 4

=============================================================================