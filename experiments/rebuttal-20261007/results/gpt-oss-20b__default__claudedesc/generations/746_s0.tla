MODULE Chameneos
EXTENDS Naturals

CONSTANTS N, M

Colors == {"blue", "red", "yellow"}
Faded == "Faded"
None  == 0

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN "yellow"
       ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN "red"
       ELSE "blue"

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Init ==
  /\ numMeetings = 0
  /\ meetingPlace = None
  /\ \A i ∈ 1..M : chameneoses[i] = [color |-> "blue", count |-> 0]

MeetAction(i) ==
  LET c_i == chameneoses[i].color
      cnt_i == chameneoses[i].count
      mp == meetingPlace
      num == numMeetings
      j == mp
      newColor == Complement(c_i, chameneoses[j].color)
  IN
    /\ (mp = None /\ num < N) /\ 
       /\ meetingPlace' = i
       /\ chameneoses' = chameneoses
       /\ numMeetings' = num
    \/ (mp = None /\ num = N) /\
       /\ chameneoses' = [chameneoses EXCEPT ![i].color = Faded]
       /\ meetingPlace' = mp
       /\ numMeetings' = num
    \/ (mp = j /\ j #= i) /\
       /\ chameneoses' = [chameneoses EXCEPT
                          ![i] = [color |-> newColor, count |-> cnt_i + 1],
                          ![j] = [color |-> newColor, count |-> chameneoses[j].count + 1]]
       /\ meetingPlace' = None
       /\ numMeetings' = num + 1

Next ==
  \E i ∈ 1..M : (chameneoses[i].color #= Faded) /\ MeetAction(i)

Spec == Init /\ [][Next]_vars

SumMet == [] (numMeetings = N -> SUM i ∈ 1..M : chameneoses[i].count = 2 * N)