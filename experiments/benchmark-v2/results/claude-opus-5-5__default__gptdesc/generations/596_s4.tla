---------------------------- MODULE CounterExampleTrace ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' \in {1, 2}
    \/ /\ x # 0
       /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

-----------------------------------------------------------------------------
(* Safety *)

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* Temporal properties *)

\* Eventually x stabilizes away from 1, or eventually it stabilizes away from 2.
\* Violated by a behavior that alternates 0 -> 1 -> 0 -> 2 -> 0 -> ...
Prop == <>[](x # 1) \/ <>[](x # 2)

\* x returns to zero infinitely often.
RecurrentZero == []<>(x = 0)

\* The negation of Prop.
NegProp == ~Prop

-----------------------------------------------------------------------------
(* Postcondition: checks the TLC-generated counterexample to Prop.
   CounterExample (from TLCExt) is a record
     [state  |-> set of <<id, stateRecord>>,
      action |-> set of <<<<id, stateRecord>>, actionRecord, <<id, stateRecord>>>>]
   The expected counterexample is the lasso
     <<x=0>> -> <<x=1>> -> <<x=0>> -> <<x=2>> -> back to state 1. *)

ExpectedStates ==
    { <<1, [x |-> 0]>>,
      <<2, [x |-> 1]>>,
      <<3, [x |-> 0]>>,
      <<4, [x |-> 2]>> }

ExpectedEdges ==
    { <<1, 2>>, <<2, 3>>, <<3, 4>>, <<4, 1>> }

PostCondition ==
    /\ CounterExample.state = ExpectedStates
    /\ Cardinality(CounterExample.action) = 4
    /\ { <<a[1][1], a[3][1]>> : a \in CounterExample.action } = ExpectedEdges
    /\ \A a \in CounterExample.action :
          /\ <<a[1][1], a[1][2]>> \in ExpectedStates
          /\ <<a[3][1], a[3][2]>> \in ExpectedStates

=============================================================================