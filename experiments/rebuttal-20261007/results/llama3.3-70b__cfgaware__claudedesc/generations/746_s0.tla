```
MODULE Chameneos

EXTENDS Integers, FiniteSets

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

Color == {"blue", "red", "yellow", "Faded"}

complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF c1 = "blue" THEN IF c2 = "red" THEN "yellow" ELSE "red"
  ELSE IF c1 = "red" THEN IF c2 = "blue" THEN "yellow" ELSE "blue"
  ELSE IF c1 = "yellow" THEN IF c2 = "blue" THEN "red" ELSE "blue"

TypeOK == 
  /\ chameneoses \in (1..M -> Color)
  /\ meetingPlace \in (1..M) \cup {<<>>}
  /\ numMeetings \in 0..N

Init ==
  /\ TypeOK
  /\ meetingPlace = <<>>
  /\ numMeetings = 0
  /\ chameneoses = [i \in 1..M |-> ["color" |-> "blue", "meetings" |-> 0]]

Next ==
  \E i \in 1..M :
    /\ chameneoses[i].color # "Faded"
    /\ (meetingPlace = <<>> /\ numMeetings < N
        /\ meetingPlace' = i
        /\ numMeetings' = numMeetings
        /\ chameneoses' = [chameneoses EXCEPT ![i] = ["color" |-> chameneoses[i].color, "meetings" |-> chameneoses[i].meetings]])
      \/ (meetingPlace = <<>> /\ numMeetings = N
          /\ meetingPlace' = <<>>
          /\ numMeetings' = numMeetings
          /\ chameneoses' = [chameneoses EXCEPT ![i] = ["color" |-> "Faded", "meetings" |-> chameneoses[i].meetings]])
      \/ (meetingPlace \in 1..M /\ meetingPlace # i
          /\ meetingPlace' = <<>>
          /\ numMeetings' = numMeetings + 1
          /\ chameneoses' = [chameneoses EXCEPT 
              ![i] = ["color" |-> complement(chameneoses[i].color, chameneoses[meetingPlace].color), "meetings" |-> chameneoses[i].meetings + 1],
              ![meetingPlace] = ["color" |-> complement(chameneoses[i].color, chameneoses[meetingPlace].color), "meetings" |-> chameneoses[meetingPlace].meetings + 1]])
      )

SumMet == numMeetings = N => (+ [chameneoses[i].meetings | i \in 1..M]) = 2 * N

Spec == Init /\ [][Next]_vars

THEOREM Spec => []SumMet
```
Note: The `THEOREM` statement at the end is used to specify that the model checker should verify the invariant `SumMet`.