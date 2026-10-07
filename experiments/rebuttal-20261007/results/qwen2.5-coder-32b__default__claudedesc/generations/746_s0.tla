------------------------------- MODULE Chameneos -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
VARIABLES chameneoses, meetingPlace, numMeetings

(* --algorithm chameneos

variables 
    chameneoses = [i \in 1..M -> <<CHOOSE c \in {"blue", "red", "yellow"}, 0>>],
    meetingPlace = <<>>,
    numMeetings = 0;

fair process (creature \in 1..M) \in
1: while TRUE do
2:     if numMeetings < N then
3:         either
4:             /\ meetingPlace = <<>>
5:             /\ chameneoses[creature][1] # "Faded"
6:             -> meetingPlace' = <<creature, chameneoses[creature][1]>>
7:         or
8:             /\ meetingPlace /= <<>>
9:             /\ meetingPlace[1] /= creature
10:            /\ chameneoses[meetingPlace[1]][1] # "Faded"
11:            /\ chameneoses[creature][1] # "Faded"
12:            -> let otherColor == chameneoses[meetingPlace[1]][1]
13:                   thisColor  == chameneoses[creature][1]
14:                   newColor   == IF otherColor = thisColor THEN thisColor
15:                                 ELSE CHOOSE c \in {"blue", "red", "yellow"} \ {otherColor, thisColor}
16:               in
17:                  /\ meetingPlace' = <<>>
18:                  /\ numMeetings' = numMeetings + 1
19:                  /\ chameneoses' = [chameneoses EXCEPT ![creature] = <<newColor, chameneoses[creature][2] + 1>>,
20:                                                   ![meetingPlace[1]] = <<newColor, chameneoses[meetingPlace[1]][2] + 1>>]
21:         end either
22:     else
23:         /\ meetingPlace = <<>>
24:         /\ chameneoses' = [chameneoses EXCEPT ![creature] = IF chameneoses[creature][1] # "Faded" THEN <<"Faded", chameneoses[creature][2]] ELSE chameneoses[creature]]
25:     end if
26: od

end algorithm *)

Init == /\ meetingPlace = <<>>
        /\ numMeetings = 0
        /\ \A i \in 1..M : LET color = CHOOSE c \in {"blue", "red", "yellow"} 
                           IN chameneoses[i] = <<color, 0>>

Next ==
    \/ \E creature \in 1..M :
        (meetingPlace = <<>> /\ numMeetings < N /\ chameneoses[creature][1] # "Faded" /\
         meetingPlace' = <<creature, chameneoses[creature][1]>>)
    \/ \E creature \in 1..M :
        (meetingPlace /= <<>> /\ meetingPlace[1] /= creature /\ numMeetings < N /\
         chameneoses[meetingPlace[1]][1] # "Faded" /\ chameneoses[creature][1] # "Faded" /\
         LET otherColor = chameneoses[meetingPlace[1]][1]
             thisColor  = chameneoses[creature][1]
             newColor   = IF otherColor = thisColor THEN thisColor
                          ELSE CHOOSE c \in {"blue", "red", "yellow"} \ {otherColor, thisColor}
         IN meetingPlace' = <<>> /\ numMeetings' = numMeetings + 1 /\
            chameneoses' = [chameneoses EXCEPT ![creature] = <<newColor, chameneoses[creature][2] + 1>>,
                                             ![meetingPlace[1]] = <<newColor, chameneoses[meetingPlace[1]][2] + 1>>])
    \/ \E creature \in 1..M :
        (numMeetings >= N /\ meetingPlace = <<>> /\
         chameneoses' = [chameneoses EXCEPT ![creature] = IF chameneoses[creature][1] # "Faded" THEN <<"Faded", chameneoses[creature][2]] ELSE chameneoses[creature]])

Spec == Init /\ [][Next]_<<meetingPlace, numMeetings, chameneoses>>

SumMet == \A i \in 1..M : LET totalMeetings = \S j \in 1..M : chameneoses[j][2]
          IN numMeetings >= N => totalMeetings = 2 * N

=============================================================================