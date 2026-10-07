---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS CREATURES, N, C0

(*
  Colors and complement
*)
Faded == "faded"
ColorsBase == {"blue", "red", "yellow"}
Colors == ColorsBase \cup {Faded}

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in ColorsBase: (c # c1) /\ (c # c2)

ASSUME
  /\ C0 \in [CREATURES -> ColorsBase]
  /\ N \in Nat

VARIABLES color, count, place, meetings

vars == << color, count, place, meetings >>

Active(c) == color[c] # Faded

Init ==
  /\ color = C0
  /\ count = [c \in CREATURES |-> 0]
  /\ place = "none"
  /\ meetings = 0

Enter(c) ==
  /\ c \in CREATURES
  /\ meetings < N
  /\ place = "none"
  /\ Active(c)
  /\ place' = c
  /\ UNCHANGED << color, count, meetings >>

Meet(c) ==
  /\ c \in CREATURES
  /\ meetings < N
  /\ place \in CREATURES
  /\ c # place
  /\ Active(c) /\ Active(place)
  /\ LET c0 == place
         col0 == color[c0]
         col1 == color[c]
         comp == Complement(col0, col1)
     IN /\ color' = [color EXCEPT ![c0] = comp, ![c] = comp]
        /\ count' = [count EXCEPT ![c0] = @ + 1, ![c] = @ + 1]
        /\ meetings' = meetings + 1
        /\ place' = "none"

Fade(c) ==
  /\ c \in CREATURES
  /\ meetings = N
  /\ Active(c)
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED << count, place, meetings >>

Next ==
  \E c \in CREATURES: Enter(c) \/ Meet(c) \/ Fade(c)

RECURSIVE Sum(_,_)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE a \in S: TRUE
       IN f[x] + Sum(f, S \ {x})

SumCounts == Sum(count, CREATURES)

TypeInv ==
  /\ color \in [CREATURES -> Colors]
  /\ count \in [CREATURES -> Nat]
  /\ place \in (CREATURES \cup {"none"})
  /\ meetings \in Nat

MeetBound == meetings <= N

ArithAtLimit == (meetings = N) => (SumCounts = 2 * N)

Inv == TypeInv /\ MeetBound /\ ArithAtLimit

Spec == Init /\ [][Next]_vars
====