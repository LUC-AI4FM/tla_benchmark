---- MODULE ZeroOneTwo ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, TLCExt

VARIABLES x

vars == <<x>>

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

\* x eventually stabilizes away from 1, or eventually stabilizes away from 2.
\* This does not hold under Spec, because x can keep returning to 1 or to 2.
Prop == <>[](x # 1) \/ <>[](x # 2)

\* x returns to zero infinitely often.
\* This holds under Spec because of WF_x(Next).
RepeatedlyZero == []<>(x = 0)

\* The negation of Prop.
NotProp == ~Prop

-----------------------------------------------------------------------------
(* Postcondition: checks the counterexample trace that TLC generates for Prop. *)
(* The trace is a lasso: 0 -> 1 -> back to 0, repeated forever.                *)

ExpectedStates ==
    { <<1, [x |-> 0]>>,
      <<2, [x |-> 1]>> }

ExpectedActions ==
    { << <<1, [x |-> 0]>>, [name |-> "Next"], <<2, [x |-> 1]>> >>,
      << <<2, [x |-> 1]>>, [name |-> "Next"], <<1, [x |-> 0]>> >> }

StateSetOf(S) == { <<s[1], s[2]>> : s \in S }

ActionSetOf(A) == { << a[1], [name |-> a[2].name], a[3] >> : a \in A }

PostCondition ==
    /\ StateSetOf(CounterExample.state) = ExpectedStates
    /\ ActionSetOf(CounterExample.action) = ExpectedActions

=============================================================================