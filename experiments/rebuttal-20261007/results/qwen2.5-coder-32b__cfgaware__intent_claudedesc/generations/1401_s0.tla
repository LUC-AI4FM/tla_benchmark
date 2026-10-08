---------------------------- MODULE InnerModule ----------------------------

VARIABLES counter

CONSTANTS MaxValue

Init == counter = 0

Next ==
    /\ counter < MaxValue
    /\ counter' = counter + 1

WF_Step == WF_vars(Next, <<counter>>)

=============================================================================