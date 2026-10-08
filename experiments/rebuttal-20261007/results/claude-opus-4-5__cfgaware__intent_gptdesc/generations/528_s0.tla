---------------------------- MODULE Specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets

VARIABLES symbols, sequence, updated

\* Define the symbols used in the specification
Sym1 == "a"
Sym2 == "b"
Sym3 == "c"

\* Initial values for the sequence
InitVal1 == 1
InitVal2 == 2
InitVal3 == 3

\* New value for the second element after update
NewVal2 == 42

\* Type invariant ensuring safety properties
TypeInvariant ==
    /\ symbols \subseteq {Sym1, Sym2, Sym3}
    /\ Len(sequence) = 3
    /\ \A i \in 1..3 : sequence[i] \in Int
    /\ updated \in BOOLEAN

\* Initial state predicate
Init ==
    /\ symbols = {Sym1, Sym2}
    /\ sequence = <<InitVal1, InitVal2, InitVal3>>
    /\ updated = FALSE

\* The single composite update step
Update ==
    /\ updated = FALSE
    /\ symbols' = symbols \union {Sym3}
    /\ sequence' = [sequence EXCEPT ![2] = NewVal2]
    /\ updated' = TRUE

\* Stuttering step for termination (system stays in final state)
Stutter ==
    /\ updated = TRUE
    /\ UNCHANGED <<symbols, sequence, updated>>

\* Next state relation
Next ==
    \/ Update
    \/ Stutter

\* Fairness condition to ensure liveness
Fairness == WF_<<symbols, sequence, updated>>(Update)

\* Complete specification with fairness for liveness
Spec ==
    /\ Init
    /\ [][Next]_<<symbols, sequence, updated>>
    /\ Fairness

\* Safety property: type invariant always holds
Safety == []TypeInvariant

\* Liveness property: eventually the update occurs
Liveness == <>(updated = TRUE)

\* Observable final state properties
FinalSetValue == {Sym1, Sym2, Sym3}
FinalSequenceValue == <<InitVal1, NewVal2, InitVal3>>

\* Property that final state has expected values
FinalStateCorrect ==
    [](updated = TRUE => 
        /\ symbols = FinalSetValue
        /\ sequence = FinalSequenceValue)

=============================================================================