------------------------------- MODULE SimpleSystem -------------------------------

CONSTANTS 
    InitialSymbols \* A set of two distinct symbols, e.g., {"A", "B"}
    InitialSequence \* A sequence of three integers, e.g., <<1, 2, 3>>
    NewSymbol \* The new symbol to be added to the set, e.g., "C"
    NewValue \* The new integer value for the second element of the sequence, e.g., 4

VARIABLES 
    symbols, sequence

Init == /\ symbols = InitialSymbols
        /\ sequence = InitialSequence

Next == \/ /\ symbols' = symbols \cup {NewSymbol}
             /\ sequence' = <<sequence[1], NewValue, sequence[3]>>
          \/ /\ symbols' = symbols
             /\ sequence' = sequence

Spec == Init /\ [][Next]_<<symbols, sequence>>

=============================================================================