---- MODULE Toggle ----
VARIABLE x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

\* Main property: the variable is always true (intentionally violated)
Prop == [](x = TRUE)

\* Additional properties for experimentation
StatePred == x = TRUE

Trivial == TRUE

XProp == x

====