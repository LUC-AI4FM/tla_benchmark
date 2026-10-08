------------------------------- MODULE SimpleSystem -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    InitialSymbols,  \* A set of two distinct symbols
    InitialSequence, \* A sequence of three integers
    NewSymbol,       \* The new symbol to be added to the set
    NewValue         \* The new integer value for the second element of the sequence

VARIABLES 
    Symbols, 
    Sequence

Init == /\ Symbols = InitialSymbols
        /\ Sequence = InitialSequence

Next == \/ /\ Symbols' = Symbols \cup {NewSymbol}
              /\ Sequence' = [Sequence EXCEPT ![2] = NewValue]
           \/ /\ Symbols' = Symbols
              /\ Sequence' = Sequence

Spec == Init /\ [][Next]_<<Symbols, Sequence>>

\* Safety properties
TypeOK == /\ Symbols \in SUBSET (InitialSymbols \cup {NewSymbol})
          /\ Sequence \in [1..3 -> Integers]
          /\ Len(Sequence) = 3

UpdateOnce ==
    \/ /\ Symbols = InitialSymbols
       /\ Sequence = InitialSequence
    \/ /\ Symbols = InitialSymbols \cup {NewSymbol}
       /\ Sequence = [InitialSequence EXCEPT ![2] = NewValue]

\* Liveness property
Termination == <>(/\ Symbols = InitialSymbols \cup {NewSymbol}
                  /\ Sequence = [InitialSequence EXCEPT ![2] = NewValue])

Invariant == TypeOK /\ UpdateOnce

THEOREM Spec => []Invariant

THEOREM Spec => Termination

=============================================================================