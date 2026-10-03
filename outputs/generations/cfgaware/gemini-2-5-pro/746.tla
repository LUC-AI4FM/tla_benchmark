---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS Chameneos, Colors, N, Noone, Complement(_,_)

ASSUME
    /\ IsFiniteSet(Chameneos)
    /\ IsFiniteSet(Colors)
    /\ Cardinality(Colors) >= 2
    /\ N \in Nat
    /\ Noone \notin Chameneos
    /\ \A c1, c2 \in Colors :
           /\ Complement(c1, c2) \in Colors
           /\ Complement(c1, c2) = Complement(c2, c1)

VARIABLES color, meetings, place, totalMeetings, pc

vars == <<color, meetings, place, totalMeetings, pc>>

Init ==
    /\ totalMeetings = 0
    /\ place = Noone
    /\ \E initial_colors \in [Chameneos -> Colors] :
           color = initial_colors
    /\ meetings = [c \in Chameneos |-> 0]
    /\ pc = [c \in Chameneos |-> "thinking"]

\* A thinking chameneos arrives at an empty meeting place.
Arrive(c) ==
    /\ pc[c] = "thinking"
    /\ totalMeetings < N
    /\ place = Noone
    /\ place' = c
    /\ pc' = [pc EXCEPT ![c] = "waiting"]
    /\ UNCHANGED <<color, meetings, totalMeetings>>

\* A thinking chameneos arrives at an occupied place and meets the creature there.
Meet(c) ==
    /\ pc[c] = "thinking"
    /\ totalMeetings < N
    /\ place \in Chameneos
    /\ LET c2 == place
           new_color == Complement(color[c], color[c2])
       IN /\ color' = [color EXCEPT ![c] = new_color, ![c2] = new_color]
          /\ meetings' = [meetings EXCEPT ![c] = @ + 1, ![c2] = @ + 1]
          /\ totalMeetings' = totalMeetings + 1
          /\ place' = Noone
          /\ pc' = [pc EXCEPT ![c] = "thinking", ![c2] = "thinking"]

\* A thinking chameneos tries to meet after the global limit is reached.
Fade(c) ==
    /\ pc[c] = "thinking"
    /\ totalMeetings = N
    /\ pc' = [pc EXCEPT ![c] = "faded"]
    /\ UNCHANGED <<color, meetings, place, totalMeetings>>

Next ==
    \/ \E c \in Chameneos :
        \/ Arrive(c)
        \/ Meet(c)
        \/ Fade(c)
    \/ UNCHANGED vars

-----------------------------------------------------------------------------
\* Definitions required by the model-checking configuration.

TypeOK ==
    /\ color \in [Chameneos -> Colors]
    /\ meetings \in [Chameneos -> Nat]
    /\ place \in Chameneos \cup {Noone}
    /\ totalMeetings \in 0..N
    /\ pc \in [Chameneos -> {"thinking", "waiting", "faded"}]

RECURSIVE SumRec(_, _)
SumRec(S, f) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN
         f[x] + SumRec(S \ {x}, f)

SumMet == SumRec(Chameneos, meetings)

Spec == Init /\ [][Next]_vars

=============================================================================