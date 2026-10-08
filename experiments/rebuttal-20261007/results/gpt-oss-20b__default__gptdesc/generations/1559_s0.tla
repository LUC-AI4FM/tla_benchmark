MODULE Peterson
EXTENDS Naturals

CONSTANTS N = 2

VARIABLES turn, flag, cs

InitP == /\ turn ∈ 0..N-1
        /\ flag = [i \in 0..N-1 |-> FALSE]
        /\ cs   = [i \in 0..N-1 |-> FALSE]

Entry(i) ==
    /\ flag[i] = FALSE
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<turn,cs>>

TurnStep(i,j) ==
    /\ turn = j
    /\ turn' = i
    /\ UNCHANGED <<flag,cs>>

WaitStep(i,j) ==
    /\ turn = i
    /\ cs'   = [cs EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<turn,flag>>

Exit(i) ==
    /\ cs[i] = TRUE
    /\ cs'   = [cs EXCEPT ![i] = FALSE]
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ UNCHANGED turn

NextP == ∨ ∀ i ∈ 0..N-1 :
            Entry(i) \/ TurnStep(i,1-i) \/ WaitStep(i,1-i) \/ Exit(i)

SpecP == InitP /\ [][NextP]_<<turn,flag,cs>>

SafetyP == ~((cs[0] /\ cs[1]))

END MODULE

MODULE LockProtocol
EXTENDS Naturals, Peterson

CONSTANTS N = 2

VARIABLES turn, flag, cs, s, h_turn

Init ==
    /\ turn ∈ 0..N-1
    /\ flag   = [i \in 0..N-1 |-> FALSE]
    /\ cs     = [i \in 0..N-1 |-> FALSE]
    /\ s      = 0
    /\ h_turn = {}

other(i) == 1 - i

EntryStep(i) ==
    /\ flag[i] = FALSE
    /\ flag'   = [flag EXCEPT ![i] = TRUE]
    /\ s'      = 1
    /\ UNCHANGED <<turn,cs,h_turn>>

TurnStep(i) ==
    /\ flag[i] = TRUE
    /\ turn = other(i)
    /\ turn' = i
    /\ s'     = 2
    /\ UNCHANGED <<flag,cs,h_turn>>

WaitStep(i) ==
    /\ flag[i] = TRUE
    /\ turn = i
    /\ cs'   = [cs EXCEPT ![i] = TRUE]
    /\ s'    = 3
    /\ UNCHANGED <<turn,flag,h_turn>>

ExitStep(i) ==
    /\ cs[i] = TRUE
    /\ cs'   = [cs EXCEPT ![i] = FALSE]
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ h_turn' = h_turn ∪ {turn}
    /\ s'      = 0
    /\ UNCHANGED turn

Next == ∨ ∀ i ∈ 0..N-1 :
            EntryStep(i) \/ TurnStep(i) \/ WaitStep(i) \/ ExitStep(i)

Spec == Init /\ [][Next]_<<turn,flag,cs,s,h_turn>>

Safety == ~((cs[0] /\ cs[1]))

InstancePeterson ==
    INSTANCE Peterson WITH
        N   -> N,
        turn-> turn,
        flag-> flag,
        cs  -> cs

END MODULE