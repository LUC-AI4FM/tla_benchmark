```
MODULE ToggleSystem
VARIABLES state

Init == state = FALSE

Next == (state' = ~state) /\ (action = "toggle1" \/ action = "toggle2")

THEOREM Spec == Init /\ [][Next]_
```