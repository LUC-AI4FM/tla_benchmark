MODULE RendezvousProtocol
EXTENDS Naturals, Sequences

CONSTANTS M, N, COLORS, NextColor

ASSUME M > 0 /\ N > 0
ASSUME ∀ s1,s2 \in COLORS : NextColor[s1,s2] = NextColor[s2,s1]
ASSUME ∀ s1,s2 \in COLORS : NextColor[s1,s2] ∈ COLORS

VARIABLES state, waiting, counter, inactive, meetingCount

StateType == [i \in 1..M |-> COLORS]
WaitingType == 0 \/ 1..M
CounterType == Nat
InactiveType == SUBSET 1..M
MeetingCountType == [i \in 1..M |-> Nat]

Init ==
    /\ state ∈ StateType
    /\ waiting = 0
    /\ counter = 0
    /\ inactive = {}
    /\ meetingCount ∈ MeetingCountType

Enter(i) ==
    /\ i ∉ inactive
    /\ waiting = 0
    /\ counter < N
    /\ waiting' = i
    /\ UNCHANGED <<state, counter, inactive, meetingCount>>

Fade(i) ==
    /\ i ∉ inactive
    /\ counter >= N
    /\ inactive' = inactive ∪ {i}
    /\ UNCHANGED <<state, waiting, counter, meetingCount>>

Meet(i) ==
    LET w == waiting IN
    /\ w ∈ 1..M
    /\ i ∈ 1..M \ {w}
    /\ i ∉ inactive
    /\ counter < N
    /\ state' = [state EXCEPT ![w] = NextColor[state[w], state[i]],
                                 ![i] = NextColor[state[w], state[i]]]
    /\ meetingCount' = [meetingCount EXCEPT ![w] = meetingCount[w] + 1,
                                   ![i] = meetingCount[i] + 1]
    /\ counter' = counter + 1
    /\ waiting' = 0
    /\ inactive' = inactive

Skip ==
    UNCHANGED <<state, waiting, counter, inactive, meetingCount>>

Next ==
    \E i \in 1..M :
        (Enter(i) \/ Fade(i) \/ Meet(i))
    \/ Skip

vars == <<state, waiting, counter, inactive, meetingCount>>

SafetyInvariant ==
    /\ waiting = 0 \/ waiting ∈ 1..M
    /\ counter <= N
    /\ inactive ⊆ 1..M
    /\ state ∈ StateType
    /\ meetingCount ∈ MeetingCountType

AccountingInvariant ==
    (counter = N) => SUM i \in 1..M : meetingCount[i] = 2*N

TerminationConsistency ==
    (counter = N) =>
        (\A i \in 1..M : i ∈ inactive \/ NOT (waiting = i))

Spec == Init /\ [][Next]_vars /\ SafetyInvariant /\ AccountingInvariant /\ TerminationConsistency
===============================================================================