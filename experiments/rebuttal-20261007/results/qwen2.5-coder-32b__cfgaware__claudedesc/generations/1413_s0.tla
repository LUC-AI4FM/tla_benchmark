---- MODULE Github790 ----

VARIABLES a

CONSTANTS Init, Next, Spec, AlwaysTrue

Init == a = 0

Next == /\ UNCHANGED a

Spec == Init /\ [][Next]_<<a>>

AlwaysTrue == <>TRUE => <>[]TRUE

====