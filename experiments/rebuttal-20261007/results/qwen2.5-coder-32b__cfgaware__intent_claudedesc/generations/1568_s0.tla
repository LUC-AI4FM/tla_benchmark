------------------------------- MODULE Bakery -------------------------------

CONSTANTS NumProcs, MaxTicket

VARIABLES choosing, number

(*--algorithm bakery
variables 
    choosing = [p \in 1..NumProcs -> FALSE],
    number   = [p \in 1..NumProcs -> 0];

process p \in 1..NumProcs
begin
Choose:
    await \A q \in 1..NumProcs : \/ ~choosing[q] \/ number[q] = 0;
    choosing[p] := TRUE;
    number[p]   := 1 + Max({number[q] : q \in 1..NumProcs});
    choosing[p] := FALSE;

RequestCS:
    await \A q \in 1..NumProcs :
            \/ ~choosing[q]
            \/ \/ number[q] = 0
               \/ number[q] < number[p]
               \/ /\ number[q] = number[p]
                  /\ q < p;

CriticalSection:
    skip;

EndCS:
    number[p] := 0;
end process;
end algorithm;)

Invariant == \A p, q \in 1..NumProcs : p # q => \/ ~choosing[p] \/ ~choosing[q] \/ number[p] = 0 \/ number[q] = 0

Spec == /\ Init
        /\ \Box [][Next]_<<choosing, number>>
        /\ \A s \in States : Invariant(s)

=============================================================================