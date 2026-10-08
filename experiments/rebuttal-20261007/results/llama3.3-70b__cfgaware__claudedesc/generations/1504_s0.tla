```
MODULE G
VARIABLE u1

Init == u1 = TRUE

Next == 
  /\ UNCHANGED <<u1>>
  /\ UNCHANGED u1
  /\ UNCHANGED vars

Prop == ENABLED Next

Spec == Init /\ [][Next]_vars
THEOREM Spec => []Prop
```
Note: The `Spec` and `THEOREM` lines are added to complete the TLA+ module, as they define the temporal specification and an invariant property to be checked. However, the core definitions of `Init`, `Next`, and `Prop` directly follow from the provided system description.