----------------------------- MODULE Chameneos -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS C, N, Nil, StartColor, Colors

VARIABLES colors, counts, meetingPlace, totalMeetings

vars == <<colors, counts, meetingPlace, totalMeetings>>

TypeInvariant ==
  /\ colors \in [C -> Colors]
  /\ counts \in [C -> Nat]
  /\ meetingPlace \in C ∪ {Nil}
  /\ totalMeetings \in Nat

Init ==
  /\ TypeInvariant
  /\ colors = [i \in C |-> StartColor]
  /\ counts = [i \in C |-> 0]
  /\ meetingPlace = Nil
  /\ totalMeetings = 0

EnterAction(i) == 
  /\ i \in C
  /\ meetingPlace = Nil
  /\ totalMeetings < N
  /\ colors' = colors
  /\ counts' = counts
  /\ meetingPlace' = i
  /\ totalMeetings' = totalMeetings

MeetAction(i, j) ==
  /\ i \in C
  /\ j \in C
  /\ i \# j
  /\ meetingPlace = i
  /\ totalMeetings < N
  /\ colors' = colors
  /\ counts'[i] = counts[i] + 1
  /\ counts'[j] = counts[j] + 1
  /\ (\A k \in C : k \# i /\ k \# j => counts'[k] = counts[k])
  /\ meetingPlace' = Nil
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \E i \in C : EnterAction(i)
  \/ \E i, j \in C : MeetAction(i, j)

SumCounts == \sum i \in C : counts[i]

SafetyInvariant == (totalMeetings = N) => SumCounts = 2 * N

Spec == Init /\ [][Next]_vars /\ SafetyInvariant
=============================================================================