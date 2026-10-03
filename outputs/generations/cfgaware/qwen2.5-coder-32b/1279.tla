------------------------------- MODULE SmallTemporalModel -------------------------------

CONSTANTS
    Next

VARIABLES
    s

ASSUME
    \A var \in Nat : Next(var) \subseteq {0, 1}

Init == s = 23

Next(s) == \/ s' \in {0, 1} /\ s' > 0
           \/ s' = s

Inv == s /= 0

Spec == Init /\ [][Next]_<<s>>

=============================================================================