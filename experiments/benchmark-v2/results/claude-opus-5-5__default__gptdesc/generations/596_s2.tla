---------------------------- MODULE ZeroOneTwo ----------------------------
EXTENDS Naturals, TLC, TLCExt

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* Initial condition and transitions                                       *)
-----------------------------------------------------------------------------

Init == x = 0

FromZero == /\ x = 0
            /\ x' \in {1, 2}

ToZero == /\ x # 0
          /\ x' = 0

Next == FromZero \/ ToZero

Spec == Init /\ [][Next]_x /\ WF_x(Next)

-----------------------------------------------------------------------------
(* Safety                                                                  *)
-----------------------------------------------------------------------------

TypeOK == x \in {0, 1, 2}

-----------------------------------------------------------------------------
(* Temporal properties                                                     *)
-----------------------------------------------------------------------------

\* Eventually x stays away from 1 forever, or eventually it stays away
\* from 2 forever. This does not hold for Spec, because x can alternate
\* 0 -> 1 -> 0 -> 2 -> 0 -> ...
Prop == <>[](x # 1) \/ <>[](x # 2)

\* x returns to zero infinitely often. This holds under WF_x(Next).
InfinitelyOftenZero == []<>(x = 0)

\* The negation of Prop. It asserts that x visits both 1 and 2
\* infinitely often.
NotProp == ~Prop

-----------------------------------------------------------------------------
(* Postcondition: checks the counterexample that TLC generates when it     *)
(* checks Prop. TLCExt!CounterExample is a record:                         *)
(*   [ state  |-> set of <<index, [x |-> v]>> tuples,                      *)
(*     action |-> set of <<<<i, s>>, actionInfo, <<j, t>>>> tuples ]       *)
(*                                                                         *)
(* The counterexample must be a lasso that visits both x = 1 and x = 2.    *)
(* Each of its steps must be a legal Next step.                            *)
-----------------------------------------------------------------------------

CEStates  == { s[2] : s \in CounterExample.state }
CEActions == CounterExample.action

PostCondition ==
    /\ CounterExample.state # {}
    /\ CEStates \subseteq [x : {0, 1, 2}]
    /\ [x |-> 0] \in CEStates
    /\ [x |-> 1] \in CEStates
    /\ [x |-> 2] \in CEStates
    /\ \A a \in CEActions :
          LET from == a[1][2].x
              to   == a[3][2].x
          IN  \/ (from = 0 /\ to \in {1, 2})
              \/ (from # 0 /\ to = 0)
=============================================================================