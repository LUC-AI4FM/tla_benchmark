MODULE Chameneos
EXTENDS Naturals, Sequences, TLC

CONSTANTS M, N

None == 0

Creatures == 1..M
Colors    == {"Blue","Red","Yellow"}

VARIABLES color, meetCount, mall, totalMeetings, faded

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c ∈ Colors : c # c1 /\ c # c2

Init ==
    /\ color \in [Creatures -> Colors]
    /\ meetCount \in [Creatures -> Nat]
    /\ ALL i ∈ Creatures : meetCount[i] = 0
    /\ mall = None
    /\ totalMeetings = 0
    /\ faded \in [Creatures -> BOOLEAN]
    /\ ALL i ∈ Creatures : faded[i] = FALSE

ArriveEmpty ==
    ∃ i ∈ Creatures :
        /\ ~faded[i]
        /\ mall = None
        /\ totalMeetings < N
        /\ mall' = i
        /\ UNCHANGED <<color, meetCount, totalMeetings, faded>>

Meet ==
    ∃ i,j ∈ Creatures :
        /\ i ≠ j
        /\ ~faded[i]
        /\ ~faded[j]
        /\ mall = j
        /\ totalMeetings < N
        /\ color'   = [color EXCEPT ![i] = Complement(color[i], color[j]),
                                 ![j] = Complement(color[i], color[j])]
        /\ meetCount'= [meetCount EXCEPT ![i] = @ + 1,
                                   ![j] = @ + 1]
        /\ totalMeetings' = totalMeetings + 1
        /\ mall'   = None
        /\ faded'  = faded

FadeEmpty ==
    ∃ i ∈ Creatures :
        /\ ~faded[i]
        /\ mall = None
        /\ totalMeetings >= N
        /\ faded'[i] = TRUE
        /\ UNCHANGED <<color, meetCount, totalMeetings, mall>>

FadeWaiting ==
    ∃ i ∈ Creatures :
        /\ ~faded[i]
        /\ mall = i
        /\ totalMeetings >= N
        /\ faded'[i] = TRUE
        /\ mall'   = None
        /\ UNCHANGED <<color, meetCount, totalMeetings, faded>>

Next == ArriveEmpty \/ Meet \/ FadeEmpty \/ FadeWaiting

TypeInvariant ==
    /\ color \in [Creatures -> Colors]
    /\ meetCount \in [Creatures -> Nat]
    /\ mall ∈ {None} ∪ Creatures
    /\ totalMeetings ∈ Nat
    /\ totalMeetings <= N
    /\ faded \in [Creatures -> BOOLEAN]
    /\ ALL i ∈ Creatures : ~faded[i] => mall # i

SumInvariant ==
    (SUM i ∈ Creatures : meetCount[i]) = 2 * totalMeetings

Spec == Init /\ [][Next]_vars /\ TypeInvariant /\ SumInvariant
===============================================================================