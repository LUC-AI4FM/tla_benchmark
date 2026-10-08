MODULE Chameneos
EXTENDS Naturals, TLC

CONSTANTS CHAMENOS, EMPTY, N

VARIABLES colors, counts, slot, totalMeetings

(* Type invariant *)
TypeInvariant ==
  /\ colors \in [CHAMENOS -> Nat]
  /\ counts \in [CHAMENOS -> Nat]
  /\ slot \in CHAMENOS \/ {EMPTY}
  /\ totalMeetings \in Nat

Init ==
  /\ colors = [i \in CHAMENOS |-> 0]
  /\ counts = [i \in CHAMENOS |-> 0]
  /\ slot   = EMPTY
  /\ totalMeetings = 0

(* Actions *)
Meet(i) ==
  /\ slot = EMPTY
  /\ totalMeetings < N
  /\ slot' = i
  /\ UNCHANGED <<colors, counts, totalMeetings>>

MeetWith(i,j) ==
  /\ i \in CHAMENOS
  /\ j \in CHAMENOS
  /\ i /= j
  /\ slot = j
  /\ totalMeetings < N
  /\ colors' = [colors EXCEPT ![i] = colors[j], ![j] = colors[i]]
  /\ counts' = [counts EXCEPT ![i] = counts[i]+1, ![j] = counts[j]+1]
  /\ slot' = EMPTY
  /\ totalMeetings' = totalMeetings + 1

Fade(i) ==
  /\ i \in CHAMENOS
  /\ totalMeetings >= N
  /\ colors' = [colors EXCEPT ![i] = 0]
  /\ UNCHANGED <<counts, slot, totalMeetings>>

Next ==
  \E i \in CHAMENOS : Meet(i)
  \/ \E i,j \in CHAMENOS : MeetWith(i,j)
  \/ \E i \in CHAMENOS : Fade(i)

(* Invariant *)
SumCounts == \sum i \in CHAMENOS : counts[i]
Inv == (totalMeetings = N) => SumCounts = 2 * N

Spec ==
  Init
  /\ [][Next]_<<colors, counts, slot, totalMeetings>>
  /\ Inv
  /\ TypeInvariant

===============================================================================