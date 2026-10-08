---- MODULE Github790 ----

EXTENDS TLC

CONSTANTS 
    (* No constants defined *)

VARIABLES a

Init == a = 0

Next == UNCHANGED a

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE

====