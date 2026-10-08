MODULE Chameneos
EXTENDS Naturals, FiniteSets

CONSTANTS CHAMENEOSES, COLORS, N, EMPTY, FADE

(* Type definitions *)
TYPEDEF Color == COLORS \cup {FADE}
TYPEDEF Slot   == CHAMENEOSES \cup {EMPTY}

VARIABLES color, meetCount, meetingSlot, totalMeetings

color        : [CHAMENEOSES -> Color]
meetCount    : [CHAMENEOSES -> Nat]
meetingSlot  : Slot
totalMeetings: Nat

(* Helper to pick an initial color *)
InitColor(i) == CHOOSE c \in COLORS : TRUE

Init ==
  /\ color      = [i \in CHAMENEOSES |-> InitColor(i)]
  /\ meetCount  = [i \in CHAMENEOSES |-> 0]
  /\ meetingSlot = EMPTY
  /\ totalMeetings = 0

Complement(c) == c

Wait(i) ==
  /\ meetingSlot = EMPTY
  /\ totalMeetings < N
  /\ meetingSlot' = i

Meeting(i,j) ==
  /\ meetingSlot = j
  /\ i # j
  /\ totalMeetings < N
  /\ meetCount[i]'   = meetCount[i] + 1
  /\ meetCount[j]'   = meetCount[j] + 1
  /\ totalMeetings'  = totalMeetings + 1
  /\ color'[i]       = Complement(color[j])
  /\ color'[j]       = Complement(color[i])
  /\ meetingSlot'    = EMPTY

Fade(i) ==
  /\ totalMeetings >= N
  /\ color' = [color EXCEPT ![i] = FADE]

Next ==
  \E i \in CHAMENEOSES :
    ( Wait(i)
      \/ (\E j \in CHAMENEOSES : j # i /\ Meeting(j,i))
      \/ Fade(i) )

SafetyInvariant ==
  (totalMeetings = N) => (\SUM i \in CHAMENEOSES : meetCount[i]) = 2 * N

vars == <<color, meetCount, meetingSlot, totalMeetings>>

Spec == Init /\ [][Next]_vars /\ SafetyInvariant
END MODULE