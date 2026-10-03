------------------------------- MODULE InitializationPattern -------------------------------

VARIABLE s

Init(var) == \E v \in 0..1 : var = v /\ var < 1

Spec == \/ <<s >> \in Init(s)
        \/ <>[UNCHANGED s]_<<s >>

Inv == s < 1

=============================================================================