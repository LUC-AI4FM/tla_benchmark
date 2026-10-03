---------------------------- MODULE SmallStateMachine ----------------------------
EXTENDS Integers

CONSTANT Init, Next, Done, Wrap
VARIABLE x

Init == (x = 0)
Next == (x' = (x + 1) % 3)
Done == (x = 2)
Wrap == (x = 2) /\ (x' = 0)

Spec == Init /\ [][Next]_x

THEOREM TLCGet("NamedStateCount", "IsOne") = 1
THEOREM TLCGet("NamedStateCount", "IsDone") = 1
THEOREM TLCGet("NamedStateCount", "DidWrap") = 1

=============================================================================