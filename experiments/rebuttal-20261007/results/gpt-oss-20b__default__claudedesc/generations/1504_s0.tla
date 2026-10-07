MODULE G
VARIABLE u1

Init == u1 = TRUE

Next ==
  /\ UNCHANGED u1
  /\ UNCHANGED <<u1>>
  /\ UNCHANGED u1

Prop == ENABLED Next

Spec == Init /\ [][Next]_<<u1>>