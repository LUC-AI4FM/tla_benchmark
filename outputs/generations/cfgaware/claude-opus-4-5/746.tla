---------------------------- MODULE Chameneos ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, Creatures, Colors

VARIABLES color, met, slot, totalMet, faded

vars == <<color, met, slot, totalMet, faded>>

\* Symmetric complement function for colors
\* Assumes Colors = {"blue", "red", "yellow"}
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
    ELSE c1  \* fallback

\* Sum of all individual meeting counters
SumMet == 
    LET Sum[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET c == CHOOSE x \in S : TRUE
             IN met[c] + Sum[S \ {c}]
    IN Sum[Creatures]

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ met \in [Creatures -> Nat]
    /\ slot \in (Creatures \union {<<>>})
    /\ totalMet \in Nat
    /\ faded \in SUBSET Creatures

Init ==
    /\ color \in [Creatures -> Colors]
    /\ met = [c \in Creatures |-> 0]
    /\ slot = <<>>
    /\ totalMet = 0
    /\ faded = {}

\* A creature enters the empty meeting place
Enter(c) ==
    /\ c \notin faded
    /\ slot = <<>>
    /\ totalMet < N
    /\ slot' = c
    /\ UNCHANGED <<color, met, totalMet, faded>>

\* A creature meets another creature already in the meeting place
Meet(c) ==
    /\ c \notin faded
    /\ slot /= <<>>
    /\ slot /= c
    /\ totalMet < N
    /\ LET other == slot
           newColor == Complement(color[c], color[other])
       IN /\ color' = [color EXCEPT ![c] = newColor, ![other] = newColor]
          /\ met' = [met EXCEPT ![c] = met[c] + 1, ![other] = met[other] + 1]
          /\ slot' = <<>>
          /\ totalMet' = totalMet + 1
          /\ UNCHANGED faded

\* A creature tries to enter but meeting limit reached, so it fades
Fade(c) ==
    /\ c \notin faded
    /\ totalMet >= N
    /\ faded' = faded \union {c}
    /\ UNCHANGED <<color, met, slot, totalMet>>

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Meet(c)
    \/ \E c \in Creatures : Fade(c)

Spec == Init /\ [][Next]_vars

\* Safety property: when total meetings reaches N, sum of individual counters equals 2*N
SafetyProperty ==
    totalMet = N => SumMet = 2 * N

=============================================================================