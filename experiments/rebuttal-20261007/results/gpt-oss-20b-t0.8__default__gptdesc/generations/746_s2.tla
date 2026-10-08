------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, TLC

CONSTANTS NumCham, N, RED, GREEN, BLUE, FADED, NONE
Ids == 1 .. NumCham

Complement(a,b) ==
  IF a = b THEN a
  ELSE IF (a = RED /\ b = GREEN \/ a = GREEN /\ b = RED) THEN BLUE
       ELSE IF (a = GREEN /\ b = BLUE \/ a = BLUE /\ b = GREEN) THEN RED
            ELSE IF (a = BLUE /\ b = RED \/ a = RED /\ b = BLUE) THEN GREEN
                 ELSE a

VARIABLES colors, meetCount, slot, totMeetings

vars == {colors, meetCount, slot, totMeetings}

Init ==
  /\ colors \in [Ids -> {RED, GREEN, BLUE, FADED}]
  /\ meetCount \in [Ids -> Nat]
  /\ slot \in Ids \/ {NONE}
  /\ totMeetings \in Nat
  /\ colors = [i \in Ids |-> RED]
  /\ meetCount = [i \in Ids |-> 0]
  /\ slot = NONE
  /\ totMeetings = 0

Enter(i) ==
  /\ i \in Ids
  /\ slot = NONE
  /\ totMeetings < N
  /\ colors' = colors
  /\ meetCount' = meetCount
  /\ slot' = i
  /\ totMeetings' = totMeetings

Meet(i) ==
  /\ i \in Ids
  /\ slot \in Ids
  /\ totMeetings < N
  /\ LET j == slot, newC == Complement(colors[i], colors[j]) IN
       /\ colors' = [colors EXCEPT ![i] = newC, ![j] = newC]
       /\ meetCount' = [meetCount EXCEPT ![i] = meetCount[i]+1,
                         ![j] = meetCount[j]+1]
       /\ totMeetings' = totMeetings + 1
       /\ slot' = NONE

Fade(i) ==
  /\ i \in Ids
  /\ totMeetings >= N
  /\ colors' = [colors EXCEPT ![i] = FADED]
  /\ meetCount' = meetCount
  /\ slot' = slot
  /\ totMeetings' = totMeetings

Next == 
   \E i \in Ids : Enter(i)
 \/ \E i \in Ids : Meet(i)
 \/ \E i \in Ids : Fade(i)

Spec == Init /\ [][Next]_vars

SafetyInv == (totMeetings = N) => (\sum i \in Ids : meetCount[i]) = 2*N

THEOREM SafeSpec : Spec => [] SafetyInv
------------------------------ END ------------------------------
