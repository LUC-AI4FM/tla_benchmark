------------------------------- MODULE ClockBit -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES bit

Init == \/ bit = TRUE
        \/ bit = FALSE

Next == /\ TYPEOK(bit)
        /\ bit' = ~bit

Spec == /\ Init
        /\ [][Next]_<<bit>>
        /\ WF_next(<<bit>>)

TYPEOK(b) == b \in {TRUE, FALSE}

Determinism == [](Next => <>(/\ Next /\ UNCHANGED <<bit>>))

Progress == [](Init => <>Next)

SafetyOfToggling == [](Next => bit' = ~bit)

Assumption == [](bit => ~~bit = bit)

=============================================================================