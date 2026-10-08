------------------------------ MODULE PersistentTautology ------------------------------
EXTENDS Naturals, TLC

CONSTANT InitVal

VARIABLE state

Init == state = InitVal
Next == UNCHANGED state

Spec == Init /\ [][Next]_state

Prop == state = TRUE

THEOREM AlwaysTrue == Spec => [] ( (<>\Prop) => <> [] Prop )

END MODULE