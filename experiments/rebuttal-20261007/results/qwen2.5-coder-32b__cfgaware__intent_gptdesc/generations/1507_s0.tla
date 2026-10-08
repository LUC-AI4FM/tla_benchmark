------------------------------- MODULE ClockBit -------------------------------

VARIABLE bit

(*--algorithm ClockBit
variables bit \in BOOLEAN;

begin
    Init:
        with bit = TRUE;
    
    next ==
        /\ bit' = ~bit
    
end algorithm;*)

Init == bit \in {TRUE, FALSE}

Next == bit' = ~bit

TypeOK == bit \in BOOLEAN

Assumption == \A b \in BOOLEAN : ~~b = b

=============================================================================