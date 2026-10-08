```
MODULE Chameneos
EXTENDS Naturals

CONSTANTS N, CHAM \* finite set of creature identifiers (subset of Nat)

VARIABLES meetingPlace, colors, counts, totalMeetings

\* --------------------------------------------------------------------
\* Helper: sum of all individual meeting counters
\* --------------------------------------------------------------------
SumCounts == SUM c \in CHAM : counts[c]

\* --------------------------------------------------------------------
\* Initialization
\* --------------------------------------------------------------------
Init ==
    /\ meetingPlace = 0
    /\ colors   = [c \in CHAM |-> "red"]
    /\ counts   = [c \in CHAM |-> 0]
    /\ totalMeetings = 0

\* --------------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------------
Enter(c) ==
    /\ c \in CHAM
    /\ meetingPlace = 0
    /\ totalMeetings < N
    /\ meetingPlace' = c
    /\ colors'   = colors
    /\ counts'   = counts
    /\ totalMeetings' = totalMeetings

Meet(c, d) ==
    /\ c \in CHAM
    /\ d \in CHAM
    /\ c # d
    /\ meetingPlace = c
    /\ totalMeetings < N
    /\ counts'   = [counts EXCEPT ![c] = @ + 1,
                         ![d] = @ + 1]
    /\ colors'   = [colors EXCEPT ![c] = colors[d],
                         ![d] = colors[c]]
    /\ meetingPlace' = 0
    /\ totalMeetings' = totalMeetings + 1

Idle ==
    /\ meetingPlace' = meetingPlace
    /\ colors'   = colors
    /\ counts'   = counts
    /\ totalMeetings' = totalMeetings

\* --------------------------------------------------------------------
\* Next-state relation (unconditional choice of an enabled action)
\* --------------------------------------------------------------------
Next ==
    (\E c \in CHAM : Enter(c))
    \/ (\E c, d \in CHAM : Meet(c,d))
    \/ Idle

\* --------------------------------------------------------------------
\* Temporal specification
\* --------------------------------------------------------------------
Spec == Init /\ [][Next]_<<meetingPlace, colors, counts, totalMeetings>>

\* --------------------------------------------------------------------
\* Safety invariant: when the global limit is reached,
\*   the sum of individual counters equals twice that limit.
\* --------------------------------------------------------------------
SafetyInvariant ==
    (totalMeetings = N) => SumCounts = 2 * N

THEOREM SafetyInvariant
```