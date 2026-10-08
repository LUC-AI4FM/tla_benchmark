```
MODULE StationarySystem
VARIABLES state

Init == (state = TRUE)

Next == state' = state

Prop == <>[]Next /= ""
```
should be rewritten to 
```
MODULE StationarySystem
VARIABLES state

Init == (state = TRUE)

Next == state' = state

Prop == [](Next => Next)
```