------------------------------- MODULE InnerModule -------------------------------
EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES counter

Init == counter = 0

Next ==
    \/ /\ counter < MaxValue
       /\ counter' = counter + 1
    \/ /\ counter >= MaxValue
       /\ counter' = counter

WF_Next == WF_vars(Next, <<counter>>)

Spec == Init /\ [][Next]_<<counter>> /\ WF_Next

=============================================================================