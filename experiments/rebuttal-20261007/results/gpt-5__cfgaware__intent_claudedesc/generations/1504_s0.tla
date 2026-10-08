---- MODULE StationaryDemo ----

VARIABLES x

Init == x = TRUE

Next == UNCHANGED x

Prop == Enabled Next

====