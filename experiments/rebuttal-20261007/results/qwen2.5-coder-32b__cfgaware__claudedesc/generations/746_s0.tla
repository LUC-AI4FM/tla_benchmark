------------------------------- MODULE Chameneos -------------------------------

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

ColorSet == {"blue", "red", "yellow"}
Colors == ColorSet \cup {"Faded"}

Complement ==
  [<<"blue", "red">> -> "yellow",
   <<"red", "blue">> -> "yellow",
   <<"blue", "yellow">> -> "red",
   <<"yellow", "blue">> -> "red",
   <<"red", "yellow">> -> "blue",
   <<"yellow", "red">> -> "blue",
   <<"blue", "blue">> -> "blue",
   <<"red", "red">> -> "red",
   <<"yellow", "yellow">> -> "yellow"]

Init ==
  /\ numMeetings = 0
  /\ meetingPlace = <<>>
  /\ \A i \in 1..M: chameneoses[i] = <<CHOOSE c \in ColorSet: TRUE, 0>>

TypeOK ==
  /\ numMeetings \in 0..N
  /\ meetingPlace \in (SUBSET (1..M)) \ {S \in SUBSET (1..M) : Cardinality(S) > 1}
  /\ \A i \in 1..M: chameneoses[i] \in Colors \X 0..N

Meet ==
  LET c == CHOOSE j \in DOMAIN chameneoses: Elem(chameneoses[j], ColorSet)
      m == CHOOSE j \in DOMAIN chameneoses: Elem(chameneoses[j], INT)
  IN
    \/ /\ meetingPlace = <<>>
       /\ numMeetings < N
       /\ c \in ColorSet
       /\ /\ meetingPlace' = <<c, m, _>>
          /\ numMeetings' = numMeetings
          /\ \A i \in 1..M: chameneoses'[i] =
              IF i = c THEN chameneoses[i]
              ELSE chameneoses[i]
    \/ /\ meetingPlace = <<>>
       /\ numMeetings = N
       /\ c \in ColorSet
       /\ /\ meetingPlace' = <<>>
          /\ numMeetings' = numMeetings
          /\ \A i \in 1..M: chameneoses'[i] =
              IF i = c THEN <<"Faded", m>>
              ELSE chameneoses[i]
    \/ /\ meetingPlace /= <<>>
       /\ LET waitingColor == fst(meetingPlace)
              waitingCount == snd(meetingPlace)
          IN
            /\ c \in ColorSet
            /\ c # waitingColor
            /\ /\ meetingPlace' = <<>>
               /\ numMeetings' = numMeetings + 1
               /\ \A i \in 1..M: chameneoses'[i] =
                   IF i = c THEN <<Complement[<<waitingColor, c>>], m + 1>>
                   ELSE IF i = waitingColor THEN <<Complement[<<c, waitingColor>>], waitingCount + 1>>
                        ELSE chameneoses[i]

Next ==
  \/ \E i \in DOMAIN chameneoses: Meet

Spec == Init /\ [][Next]_<<chameneoses, meetingPlace, numMeetings>>

SumMet ==
  numMeetings = N => (\A i \in 1..M: LET m == snd(chameneoses[i]) IN TRUE) /\ (\E s \in SUBSET 1..M: \A i \in s: Elem(chameneoses[i], INT) = 2)

=============================================================================