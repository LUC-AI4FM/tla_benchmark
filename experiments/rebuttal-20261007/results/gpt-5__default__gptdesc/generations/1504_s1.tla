------------------------------ MODULE OneVarStuttering ------------------------------

EXTENDS Naturals

CONSTANTS C

VARIABLES u1

vars == <<u1>>

Init == u1 = TRUE

Next ==
  /\ UNCHANGED u1
  /\ UNCHANGED <<u1>>
  /\ UNCHANGED vars

Prop == ENABLED Next

Spec == Init /\ [][Next]_vars

=============================================================================