```tla
MODULE Chameneos

EXTENDS Integers, FiniteSets

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

Init ==
  /\ chameneoses = [i \in 1..M |-> <<ChooseColor(i), 0>>]
  /\ meetingPlace = nil
  /\ numMeetings = 0

Next ==
  \E i \in 1..M :
    IF chameneoses[i] # <<Faded, _>>
    THEN
      IF meetingPlace = nil
      THEN
        IF numMeetings < N
        THEN
          /\ meetingPlace' = i
          /\ chameneoses' = [chameneoses EXCEPT ![i] = <<chameneoses[i][1], chameneoses[i][2]>>]
          /\ numMeetings' = numMeetings
        ELSE
          /\ chameneoses' = [chameneoses EXCEPT ![i] = <<Faded, 0>>]
          /\ meetingPlace' = nil
          /\ numMeetings' = numMeetings
      ELSE
        IF meetingPlace # i
        THEN
          /\ chameneoses' = [chameneoses EXCEPT
                              ![meetingPlace] = <<ComplementColor(chameneoses[meetingPlace][1], chameneoses[i][1]), chameneoses[meetingPlace][2] + 1>>
                              ![i] = <<ComplementColor(chameneoses[meetingPlace][1], chameneoses[i][1]), chameneoses[i][2] + 1>>]
          /\ meetingPlace' = nil
          /\ numMeetings' = numMeetings + 1
        ELSE
          /\ chameneoses' = chameneoses
          /\ meetingPlace' = meetingPlace
          /\ numMeetings' = numMeetings
    ELSE
      /\ chameneoses' = chameneoses
      /\ meetingPlace' = meetingPlace
      /\ numMeetings' = numMeetings

Spec == Init /\ [][Next]_vars

ComplementColor(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE IF c1 = "blue"
       THEN IF c2 = "red" THEN "yellow" ELSE "red"
       ELSE IF c1 = "red"
            THEN IF c2 = "blue" THEN "yellow" ELSE "blue"
            ELSE IF c2 = "blue" THEN "red" ELSE "blue"

ChooseColor(i) == CHOOSE c \in {"blue", "red", "yellow"} : TRUE

SumMet == (numMeetings = N) => (+ chameneoses[i][2] : i \in 1..M) = 2 * N

THEOREM Spec => []SumMet
```