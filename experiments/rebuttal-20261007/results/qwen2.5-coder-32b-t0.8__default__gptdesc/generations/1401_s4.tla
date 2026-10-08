------------------------------ MODULE CounterSystem ------------------------------

EXTENDS Integers

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES 
    outerX

MODULE InnerModule(V) 
    VARIABLES x
    VARIABLE_DEF x == V
    Init == x = 0
    Next == \/ x < 3 -> x' = x + 1
            \/ x >= 3 -> x' = x
    WF_Step == WF_vars(Next, <<x>>, x < 3)
END MODULE

INSTANCE InnerModule <<outerX>>

Init == outerX = 0

Next == \/ Enabled_step -> \E newOuterX \in Nat : /\ outerX' = newOuterX
                                       /\ INSTANCE_VARIABLES!step
                                       /\ Let <<newInnerX>> \in [<<x>>, {newOuterX}] @@ INSTANCE_VARIABLES!step
                                          IN newInnerX = outerX'
                 \/ ~Enabled_step -> outerX' = outerX

Spec == Init /\ [][Next]_<<outerX>>

Live == <>[](outerX = 3)

WF_spec == WF_vars(Next, <<outerX>>, Enabled_step)

=============================================================================