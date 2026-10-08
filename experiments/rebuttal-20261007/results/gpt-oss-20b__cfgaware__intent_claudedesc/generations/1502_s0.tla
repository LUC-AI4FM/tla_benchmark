------------------------------ MODULE DemoOpSubstitution ------------------------------
CONSTANT Op
VARIABLE x

Init == x = 0

Next == x' ∈ Op(x)

Forty2(_) == SUBSET {1, 2, 3}

Spec == Init /\ [][Next]_x

=============================================================================