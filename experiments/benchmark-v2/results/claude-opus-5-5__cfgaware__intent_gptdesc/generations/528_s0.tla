---------------------------- MODULE SetSeqUpdate ----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLES symbols, seq, pc

vars == <<symbols, seq, pc>>

\* Symbols are modeled as strings
Symbols == {"a", "b", "c"}

InitSymbols == {"a", "b"}
NewSymbol   == "c"
InitSeq     == <<1, 2, 3>>
NewValue    == 42

TypeOK ==
    /\ symbols \subseteq Symbols
    /\ seq \in [1..3 -> Int]
    /\ Len(seq) = 3
    /\ pc \in {"start", "done"}

Init ==
    /\ symbols = InitSymbols
    /\ seq = InitSeq
    /\ pc = "start"

Update ==
    /\ pc = "start"
    /\ symbols' = symbols \cup {NewSymbol}
    /\ seq' = [seq EXCEPT ![2] = NewValue]
    /\ pc' = "done"

Terminating ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Update \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Update)

----------------------------------------------------------------------------
\* Safety properties

FinalStateCorrect ==
    pc = "done" =>
        /\ symbols = InitSymbols \cup {NewSymbol}
        /\ seq = [InitSeq EXCEPT ![2] = NewValue]

InitialStateCorrect ==
    pc = "start" =>
        /\ symbols = InitSymbols
        /\ seq = InitSeq

Safety == TypeOK /\ FinalStateCorrect /\ InitialStateCorrect

OnlyUpdateChanges ==
    [][ (symbols' # symbols \/ seq' # seq) => Update ]_vars

\* Liveness property
Termination == <>(pc = "done")

FinalStable == [](pc = "done" => [](pc = "done"))

=============================================================================