---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS
    N,            \* The total number of meetings to be held
    Cham,         \* The set of Chameneos IDs
    Color,        \* The set of colors
    InitialColor  \* The initial color of each Chameneos

ASSUME
    /\ N \in Nat
    /\ IsFiniteSet(Cham) /\ Cardinality(Cham) >= 2
    /\ IsFiniteSet(Color) /\ Cardinality(Color) = 3
    /\ InitialColor \in [Cham -> Color]

VARIABLES
    color,          \* The current color of each chameneos: [Cham -> Color]
    meetings,       \* The meeting count for each chameneos: [Cham -> Nat]
    total_meetings, \* The total number of meetings held so far
    meeting_place,  \* The shared meeting place, holds one chameneos or is empty
    faded           \* The set of chameneos that have faded

\* A value representing an empty meeting place, distinct from any chameneos ID.
Nil == CHOOSE v : v \notin Cham

vars == <<color, meetings, total_meetings, meeting_place, faded>>

\* The symmetric color complement rule.
\* If colors are the same, they remain. If different, they become the third color.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color : c \notin {c1, c2}

\* Helper operator to sum the values of a function over a domain.
RecursiveSum(S, f) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE x \in S: TRUE
         IN f[x] + RecursiveSum(S \ {x}, f)

Init ==
    /\ color = InitialColor
    /\ meetings = [c \in Cham |-> 0]
    /\ total_meetings = 0
    /\ meeting_place = Nil
    /\ faded = {}

(* A non-faded chameneos c arrives at an empty meeting place. *)
Arrive(c) ==
    /\ c \notin faded
    /\ total_meetings < N
    /\ meeting_place = Nil
    /\ meeting_place' = c
    /\ UNCHANGED <<color, meetings, total_meetings, faded>>

(* A non-faded chameneos c2 arrives where c1 is waiting; they meet. *)
Meet(c2) ==
    /\ \E c1 \in Cham:
        /\ meeting_place = c1
        /\ c2 # c1
        /\ c2 \notin faded
        /\ total_meetings < N
        /\ LET new_color == Complement(color[c1], color[c2])
           IN color' = [color EXCEPT ![c1] = new_color, ![c2] = new_color]
        /\ meetings' = [meetings EXCEPT ![c1] = @ + 1, ![c2] = @ + 1]
        /\ total_meetings' = total_meetings + 1
        /\ meeting_place' = Nil
        /\ UNCHANGED faded

(* A non-faded chameneos attempts to act after N meetings have occurred. *)
Fade(c) ==
    /\ c \notin faded
    /\ total_meetings >= N
    /\ faded' = faded \cup {c}
    /\ UNCHANGED <<color, meetings, total_meetings, meeting_place>>


Next ==
    \E c \in Cham:
        \/ Arrive(c)
        \/ Meet(c)
        \/ Fade(c)

Spec == Init /\ [][Next]_vars

=============================================================================