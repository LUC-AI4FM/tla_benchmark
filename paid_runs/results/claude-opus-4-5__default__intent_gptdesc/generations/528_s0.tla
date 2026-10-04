---------------------------- MODULE StateTransition ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Sym1,       \* First initial symbol
    Sym2,       \* Second initial symbol
    Sym3,       \* Symbol to be added
    InitVal1,   \* Initial value for sequence position 1
    InitVal2,   \* Initial value for sequence position 2
    InitVal3,   \* Initial value for sequence position 3
    NewVal2     \* New value for sequence position 2 after update

VARIABLES
    symbols,    \* The set of symbols
    seq,        \* The sequence of integers
    updated     \* Flag indicating whether the update has occurred

vars == <<symbols, seq, updated>>

TypeInvariant ==
    /\ symbols \subseteq {Sym1, Sym2, Sym3}
    /\ Cardinality(symbols) >= 2
    /\ Len(seq) = 3
    /\ \A i \in 1..3 : seq[i] \in Int
    /\ updated \in BOOLEAN

Init ==
    /\ symbols = {Sym1, Sym2}
    /\ seq = <<InitVal1, InitVal2, InitVal3>>
    /\ updated = FALSE

Update ==
    /\ updated = FALSE
    /\ symbols' = symbols \union {Sym3}
    /\ seq' = [seq EXCEPT ![2] = NewVal2]
    /\ updated' = TRUE

Stutter ==
    /\ updated = TRUE
    /\ UNCHANGED vars

Next ==
    \/ Update
    \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Update)

\* Safety: The set is always a valid set of symbols (sets have no duplicates by definition)
\* and the sequence always has length 3 with integer values
SafetyInvariant ==
    /\ symbols \subseteq {Sym1, Sym2, Sym3}
    /\ Len(seq) = 3
    /\ \A i \in 1..3 : seq[i] \in Int

\* Safety: Only allowed transitions are the single update or stuttering
\* Before update: symbols = {Sym1, Sym2}, seq[2] = InitVal2
\* After update: symbols = {Sym1, Sym2, Sym3}, seq[2] = NewVal2
ValidStates ==
    \/ (~updated /\ symbols = {Sym1, Sym2} /\ seq = <<InitVal1, InitVal2, InitVal3>>)
    \/ (updated /\ symbols = {Sym1, Sym2, Sym3} /\ seq = <<InitVal1, NewVal2, InitVal3>>)

\* Liveness: Eventually the update occurs
EventuallyUpdated == <>(updated = TRUE)

\* After update, the new values are observable
ObservabilityAfterUpdate ==
    updated => (symbols = {Sym1, Sym2, Sym3} /\ seq[2] = NewVal2)

================================================================================