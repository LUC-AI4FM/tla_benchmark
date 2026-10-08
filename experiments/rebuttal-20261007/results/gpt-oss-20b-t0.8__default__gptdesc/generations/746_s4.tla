MODULE Chameneos
EXTENDS Naturals

CONSTANTS N, Creatures

VARIABLES color, meetCount, slot, totalMeetings

Complement(c) == IF c = 0 THEN 1 ELSE 0

Init ==
   /\ color = [i \in Creatures |-> 0]
   /\ meetCount = [i \in Creatures |-> 0]
   /\ slot = "None"
   /\ totalMeetings = 0

Wait(i) ==
   /\ slot = "None"
   /\ slot' = i
   /\ color' = color
   /\ meetCount' = meetCount
   /\ totalMeetings' = totalMeetings

Meet(i, j) ==
   /\ slot = j
   /\ i /= j
   /\ totalMeetings < N
   /\ slot' = "None"
   /\ color' = [k \in Creatures |-> IF k=i THEN Complement(color[j])
                                 ELSE IF k=j THEN Complement(color[i])
                                 ELSE color[k]]
   /\ meetCount' = [k \in Creatures |-> IF k=i THEN meetCount[i]+1
                                   ELSE IF k=j THEN meetCount[j]+1
                                   ELSE meetCount[k]]
   /\ totalMeetings' = totalMeetings + 1

Fade(i) ==
   /\ totalMeetings >= N
   /\ slot' = "None"
   /\ color' = color
   /\ meetCount' = meetCount
   /\ totalMeetings' = totalMeetings

Next == \E i \in Creatures: Wait(i)
      \/ \E i, j \in Creatures : (i /= j) /\ Meet(i, j)
      \/ \E i \in Creatures: Fade(i)

SumMeetings == \sum_{i \in Creatures} meetCount[i]

Inv == (totalMeetings = N) => SumMeetings = 2 * N

Spec == Init /\ [][Next]_<<color, meetCount, slot, totalMeetings>> /\ Inv
=============================================================================