------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Ids, Colors

VARIABLE colors, counts, slot, totalMeetings

vars == <<colors, counts, slot, totalMeetings>>

Complement(c1, c2) ==
  CHOOSE c \in Colors : c # c1 /\ c # c2

InitColor ==
  CHOOSE c \in Colors : TRUE

Init ==
  /\ colors = [i \in Ids |-> InitColor]
  /\ counts = [i \in Ids |-> 0]
  /\ slot = "Empty"
  /\ totalMeetings = 0

Next ==
  \/ (totalMeetings < N /\
      \E i, j \in Ids : i # j /\
        LET c1 == colors[i] ; c2 == colors[j] IN
          IF c1 = c2 THEN
            /\ counts' = [counts EXCEPT ![i] = @ + 1, ![j] = @ + 1]
            /\ colors' = colors
            /\ slot' = "Empty"
            /\ totalMeetings' = totalMeetings + 1
          ELSE
            LET newColor == Complement(c1,c2) IN
              /\ colors' = [colors EXCEPT ![i] = newColor, ![j] = newColor]
              /\ counts' = [counts EXCEPT ![i] = @ + 1, ![j] = @ + 1]
              /\ slot' = "Empty"
              /\ totalMeetings' = totalMeetings + 1
        )
   \/ (totalMeetings >= N /\
       colors' = colors /\ counts' = counts /\ slot' = slot /\ totalMeetings' = totalMeetings)

TypeOK ==
  /\ colors \in [Ids -> Colors]
  /\ counts \in [Ids -> Nat]
  /\ slot \in {"Empty"} \cup Colors
  /\ totalMeetings \in Nat
  /\ totalMeetings <= N

SumMet ==
  (totalMeetings = N) => ((SUM i \in Ids : counts[i]) = 2 * N)

Spec == Init /\ [][Next]_vars

=============================================================================