MODULE SingleVarInit
EXTENDS Naturals

VARIABLES s

Init(var) == ∃v ∈ 0..1 : (var = v /\ var < 1)

Next == UNCHANGED <<s>>

Inv == s < 1

Spec == Init(s) /\ [] [Next]_<<s>> /\ [] Inv