------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals

CONSTANTS N, M
ASSUME N >= 0 /\ M > 0

VARIABLES chameneoses, meetingPlace, numMeetings

(* Colors *)
ColorSet == {"blue", "red", "yellow"} \cup {Faded}
Faded == "Faded"

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c ∈ {"blue","red","yellow"} : c # c1 /\ c # c2

(* Type invariant *)
TypeOK ==
    /\ chameneoses \in [ 1..M -> [color: ColorSet, meets: Nat] ]
    /\ meetingPlace \in {0} \cup (1..M)
    /\ numMeetings \in Nat
    /\ (\A i ∈ 1..M : chameneoses[i].meets >= 0)

(* Initial state *)
Init ==
    /\ numMeetings = 0
    /\ meetingPlace = 0
    /\ chameneoses = [i \in 1..M |-> [color |-> "blue", meets |-> 0]]

(* Meet action for creature i *)
Meet(i) ==
    /\ i ∈ 1..M
    /\ chameneoses[i].color # Faded
    /\ IF meetingPlace = 0 /\ numMeetings < N THEN
            /\ meetingPlace' = i
            /\ UNCHANGED <<chameneoses, numMeetings>>
       ELSEIF meetingPlace = 0 /\ numMeetings = N THEN
            /\ chameneoses' = [chameneoses EXCEPT ![i].color = Faded]
            /\ UNCHANGED <<meetingPlace, numMeetings>>
       ELSEIF (meetingPlace # i) /\ meetingPlace # 0 /\ chameneoses[meetingPlace].color # Faded THEN
            LET j == meetingPlace
                newColor == Complement(chameneoses[i].color, chameneoses[j].color)
            IN
                /\ chameneoses' = [chameneoses EXCEPT ![i].color = newColor,
                                            ![j].color = newColor,
                                            ![i].meets = @ + 1,
                                            ![j].meets = @ + 1]
                /\ meetingPlace' = 0
                /\ numMeetings' = numMeetings + 1
       ELSE
            FALSE

(* Next-state relation *)
Next ==
    \E i ∈ 1..M : Meet(i)

vars == <<chameneoses, meetingPlace, numMeetings>>

Spec == Init /\ [][Next]_vars

(* Invariant: sum of personal counts equals 2*N when meetings finished *)
SumMet ==
    (numMeetings = N) => (SUM i ∈ 1..M : chameneoses[i].meets) = 2 * N
===============================================================================