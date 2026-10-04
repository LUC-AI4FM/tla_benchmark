---------------------------- MODULE specification ----------------------------

VARIABLE x

Init == x = TRUE

Next == UNCHANGED x

Prop == ENABLED Next

=============================================================================