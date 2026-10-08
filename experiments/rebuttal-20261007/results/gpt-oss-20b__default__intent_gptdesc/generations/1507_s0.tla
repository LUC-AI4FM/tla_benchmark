MODULE ClockBit
VARIABLE b

Init == b \in BOOLEAN

Next == (b' = ~b)

Spec == Init /\ [][Next]_<<b>>

TypeSafe          ==  b \in BOOLEAN
ToggleSafety      ==  b' = ~b
NoDeadlock        ==  \E b' : (b' = ~b)
DoubleNegAssumption == (~(~b)) = b

SafetyInvariants   == TypeSafe /\ ToggleSafety
LivenessProperties == NoDeadlock
===============================================================================