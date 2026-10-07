------------------------------ MODULE OneVarStutter ------------------------------

EXTENDS TLC

CONSTANTS DUMMY

VARIABLES u1

vars == << u1 >>

Init == u1 = TRUE

Next ==
    /\ u1' = u1
    /\ <<u1'>> = <<u1>>
    /\ UNCHANGED u1

Prop == ENABLED Next

Spec == Init /\ [][Next]_vars

=============================================================================