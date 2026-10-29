---------------------------- MODULE SetSeqUpdate ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Symbols,          \* universe of symbols
    S1, S2,           \* the two distinct initial symbols
    NewSym,           \* the symbol added by the update step
    V1, V2, V3,       \* initial integer values of the sequence
    NewVal            \* new integer value written into position 2

ASSUME SymAssumptions ==
    /\ S1 \in Symbols
    /\ S2 \in Symbols
    /\ NewSym \in Symbols
    /\ S1 # S2

ASSUME IntAssumptions ==
    /\ V1 \in Int
    /\ V2 \in Int
    /\ V3 \in Int
    /\ NewVal \in Int

VARIABLES
    syms,   \* the finite set of symbols
    seq,    \* the length-3 sequence of integers
    pc      \* program counter: "start" or "done"

vars == <<syms, seq, pc>>

InitSyms == {S1, S2}
InitSeq  == <<V1, V2, V3>>
FinalSyms == InitSyms \cup {NewSym}
FinalSeq  == [InitSeq EXCEPT ![2] = NewVal]

-----------------------------------------------------------------------------

Init ==
    /\ syms = InitSyms
    /\ seq  = InitSeq
    /\ pc   = "start"

\* The single composite update step: add a symbol and overwrite element 2.
Update ==
    /\ pc = "start"
    /\ syms' = syms \cup {NewSym}
    /\ seq'  = [seq EXCEPT ![2] = NewVal]
    /\ pc'   = "done"

\* After termination the system stutters forever (no deadlock).
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Update \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Update)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ syms \subseteq Symbols
    /\ IsFiniteSet(syms)
    /\ seq \in Seq(Int)
    /\ Len(seq) = 3
    /\ \A i \in 1..3 : seq[i] \in Int
    /\ pc \in {"start", "done"}

\* Before the update the state is the initial state.
StartState ==
    pc = "start" => (syms = InitSyms /\ seq = InitSeq)

\* Observability: updated values are visible immediately after the update.
FinalState ==
    pc = "done" => (syms = FinalSyms /\ seq = FinalSeq)

Safety == TypeOK /\ StartState /\ FinalState

\* The only value-changing transition is the single composite update.
OnlyUpdateChanges ==
    [][ \/ /\ pc = "start"
           /\ pc' = "done"
           /\ syms' = syms \cup {NewSym}
           /\ seq'  = [seq EXCEPT ![2] = NewVal]
        \/ UNCHANGED vars ]_vars

\* Once done, the system stays done with unchanged values.
StaysDone ==
    [][pc = "done" => UNCHANGED vars]_vars

-----------------------------------------------------------------------------
\* Liveness properties

EventuallyUpdated == <>(pc = "done")

EventuallyFinalForever == <>[](pc = "done" /\ syms = FinalSyms /\ seq = FinalSeq)

-----------------------------------------------------------------------------

THEOREM Spec => []Safety
THEOREM Spec => OnlyUpdateChanges /\ StaysDone
THEOREM Spec => EventuallyUpdated /\ EventuallyFinalForever

=============================================================================