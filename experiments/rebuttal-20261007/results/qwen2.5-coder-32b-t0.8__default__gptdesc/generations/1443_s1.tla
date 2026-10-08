------------------------------- MODULE SmallStateMachine -------------------------------

EXTENDS Naturals, TLC, TLCGet

CONSTANTS
    \* No constants needed for this simple machine

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x = 0 \/ x = 1 \/ x = 2
       /\ x' = (x + 1) % 3

Spec ==
    Init /\ [][Next]_<<x>>

StateIsOne == x = 1
AllWorkDone == x = 2
WrapToZero == x = 2 /\ x' = 0

(* Fairness conditions can be added if needed, but not explicitly required *)
\* WF_x(Next)

====