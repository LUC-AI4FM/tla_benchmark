--------------------------- MODULE Chameneos ---------------------------
EXTENDS Naturals, FiniteSets

(*
  Constants:
    - CHAMS: a finite, nonempty set of chameneos identifiers
    - COLORS: a nonempty set of colors
    - Complement: symmetric complement function on colors, with c ∘ c = c
    - N: natural meeting limit
*)
CONSTANTS CHAMS, COLORS, Complement, N

ASSUME
  /\ CHAMS /= {}
  /\ IsFiniteSet(CHAMS)
  /\ COLORS /= {}
  /\ Complement \in [COLORS \X COLORS -> COLORS]
  /\ \A c \in COLORS: Complement[<<c, c>>] = c
  /\ \A a \in COLORS: \A b \in COLORS: Complement[<<a, b>>] = Complement[<<b, a>>]
  /\ N \in Nat

VARIABLES color, mcount, place, total, faded

vars == << color, mcount, place, total, faded >>

(*
  AddOver(S, f) sums the values f[x] over a finite set S.
*)
RECURSIVE AddOver(_, _)
AddOver(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN f[x] + AddOver(S \ {x}, f)

SumCounters == AddOver(CHAMS, mcount)

TypeInv ==
  /\ color \in [CHAMS -> COLORS]
  /\ mcount \in [CHAMS -> Nat]
  /\ place \in {"None"} \cup [who: CHAMS, col: COLORS]
  /\ total \in Nat /\ total <= N
  /\ faded \subseteq CHAMS

Init ==
  /\ color \in [CHAMS -> COLORS]
  /\ mcount = [i \in CHAMS |-> 0]
  /\ place = "None"
  /\ total = 0
  /\ faded = {}

Wait(i) ==
  /\ i \in CHAMS
  /\ i \notin faded
  /\ total < N
  /\ place = "None"
  /\ place' = [who |-> i, col |-> color[i]]
  /\ UNCHANGED << color, mcount, total, faded >>

Meet(i) ==
  /\ i \in CHAMS
  /\ i \notin faded
  /\ total < N
  /\ place /= "None"
  /\ i /= place.who
  /\ LET newc == Complement[<<place.col, color[i]>>]
     IN
        /\ color'  = [color EXCEPT ![place.who] = newc, ![i] = newc]
        /\ mcount' = [mcount EXCEPT ![place.who] = @ + 1, ![i] = @ + 1]
        /\ total'  = total + 1
        /\ place'  = "None"
        /\ faded'  = faded

FadeFromPlace ==
  /\ total = N
  /\ place /= "None"
  /\ faded' = faded \cup {place.who}
  /\ place' = "None"
  /\ UNCHANGED << color, mcount, total >>

FadeAlone(i) ==
  /\ i \in CHAMS
  /\ total = N
  /\ i \notin faded
  /\ faded' = faded \cup {i}
  /\ UNCHANGED << color, mcount, place, total >>

Next ==
  \E i \in CHAMS:
      Wait(i) \/ Meet(i) \/ FadeAlone(i)
  \/ FadeFromPlace

Spec == Init /\ [][Next]_vars

(*
  Safety-style arithmetic property:
  When the total number of meetings reaches N, the sum of all individual
  meeting counters equals 2*N.
*)
CountAtN ==
  (total = N) => (SumCounters = 2 * N)
=============================================================================