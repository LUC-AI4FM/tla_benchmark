------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, TLC

CONSTANTS M, N

ASSUME M >= 1 /\ N >= 0

None == 0
FadedColor == "Faded"
Colors == {"Blue", "Red", "Yellow"}
AllColors == Colors ∪ {FadedColor}
Creatures == 1 .. M

VARIABLES color, meetCount, mall, totalMeetings

vars == <<color, meetCount, mall, totalMeetings>>

TypeOK ==
    /\ color ∈ [Creatures -> AllColors]
    /\ meetCount ∈ [Creatures -> Nat]
    /\ mall ∈ {None} ∪ Creatures
    /\ totalMeetings ∈ 0..N

Init ==
    /\ color ∈ [Creatures -> Colors]
    /\ meetCount = [i \in Creatures |-> 0]
    /\ mall = None
    /\ totalMeetings = 0

ThirdColor(c1, c2) ==
    IF c1 = c2 THEN c1 ELSE
        CHOOSE c ∈ Colors : c /= c1 /\ c /= c2

Wait(i) ==
    /\ i \in Creatures
    /\ mall = None
    /\ totalMeetings < N
    /\ color[i] /= FadedColor
    /\ UNCHANGED <<meetCount, totalMeetings>>
    /\ mall' = i

Meet(i,j) ==
    LET newColor == IF color[i