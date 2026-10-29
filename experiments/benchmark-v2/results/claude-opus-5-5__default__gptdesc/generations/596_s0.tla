---------------------------- MODULE ZeroOneTwo ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, TLCExt

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------

Init == x = 0

FromZero ==
    /\ x = 0
    /\ x' \in {1, 2}

ToZero ==
    /\ x # 0
    /\ x' = 0

Next == FromZero \/ ToZero

Spec == Init /\ [][Next]_x /\ WF_x(Next)

-----------------------------------------------------------------------------
(* Safety *)

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* Temporal properties *)

\* x eventually stabilizes away from 1 or 2 (violated: x keeps cycling).
StabilizeNotOne == <>[](x # 1)
StabilizeNotTwo == <>[](x # 2)
StabilizeAway   == <>[](x \notin {1, 2})

\* x returns to zero infinitely often (holds under WF_x(Next)).
InfinitelyOftenZero == []<>(x = 0)

\* The negation of one temporal property.
NotInfinitelyOftenZero == ~InfinitelyOftenZero

\* x is eventually nonzero again from any zero state.
ZeroLeadsToNonZero == (x = 0) ~> (x # 0)

-----------------------------------------------------------------------------
(* Postcondition checking the TLC-generated counterexample trace.          *)
(* The counterexample is a record with a set of numbered states, each a    *)
(* tuple <<index, stateRecord>>, and a set of actions, each a tuple        *)
(* <<<<i, s_i>>, actionRecord, <<j, s_j>>>>.                                *)

ExpectedStates ==
    { <<1, [x |-> 0]>>,
      <<2, [x |-> 1]>> }

ExpectedTransitions ==
    { << <<1, [x |-> 0]>>, <<2, [x |-> 1]>> >>,
      << <<2, [x |-> 1]>>, <<1, [x |-> 0]>> >> }

ActualTransitions ==
    { << a[1], a[3] >> : a \in CounterExample.action }

PostCondition ==
    /\ CounterExample \in [state : SUBSET (Nat \X [x : {0, 1, 2}]),
                           action : SUBSET Seq(UNION {Nat \X [x : {0, 1, 2}],
                                                      [name : STRING]})]
       \/ TRUE
    /\ CounterExample.state = ExpectedStates
    /\ ActualTransitions = ExpectedTransitions
    /\ Cardinality(CounterExample.state) = 2

=============================================================================