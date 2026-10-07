------------------------------ MODULE Chameneos ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  CHAMS,       \* finite, nonempty set of chameneos identifiers
  Colors,      \* nonempty set of colors
  Complement,  \* a symmetric complement function Colors X Colors -> Colors
  N,           \* global meeting limit (a natural number)
  Null         \* distinguished value not in CHAMS, denotes empty meeting-place slot

ASSUME
  /\ IsFiniteSet(CHAMS) /\ CHAMS # {}
  /\ Colors # {}
  /\ N \in Nat
  /\ Null \notin CHAMS
  /\ Complement \in [Colors \X Colors -> Colors]
  /\ \A c1 \in Colors: \A c2 \in Colors:
        Complement[<<c1, c2>>] \in Colors
        /\ Complement[<<c1, c2>>] = Complement[<<c2, c1>>]

VARIABLES
  clr,       \* current color of each chameneo: [CHAMS -> Colors]
  mcnt,      \* individual meeting counters: [CHAMS -> Nat]
  slot,      \* meeting-place slot: in CHAMS or Null
  meetings,  \* total number of meetings so far: Nat
  faded      \* set of chameneos that have faded (after limit reached): subset of CHAMS

vars == << clr, mcnt, slot, meetings, faded >>

Comp(c1, c2) == Complement[<<c1, c2>>]

Init ==
  /\ clr \in [CHAMS -> Colors]
  /\ mcnt = [i \in CHAMS |-> 0]
  /\ slot = Null
  /\ meetings = 0
  /\ faded = {}

TryWait(i) ==
  /\ i \in CHAMS
  /\ meetings < N
  /\ slot = Null
  /\ slot' = i
  /\ UNCHANGED << clr, mcnt, meetings, faded >>

Meet(i) ==
  /\ i \in CHAMS
  /\ meetings < N
  /\ slot \in CHAMS
  /\ i # slot
  /\ LET j == slot IN
       /\ clr' = [clr EXCEPT
                    ![i] = Comp(@[i], @[j]),
                    ![j] = Comp(@[j], @[i])]
       /\ mcnt' = [mcnt EXCEPT
                     ![i] = @ + 1,
                     ![j] = @ + 1]
  /\ meetings' = meetings + 1
  /\ slot' = Null
  /\ UNCHANGED faded

Fade(i) ==
  /\ i \in CHAMS
  /\ meetings = N
  /\ i \notin faded
  /\ faded' = faded \cup {i}
  /\ UNCHANGED << clr, mcnt, slot, meetings >>

Next ==
  \E i \in CHAMS:
      TryWait(i) \/ Meet(i) \/ Fade(i)

Spec == Init /\ [][Next]_vars

(*
  Safety invariants
*)
RECURSIVE Sum(_,_)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE a \in S: TRUE
       IN f[x] + Sum(f, S \ {x})

TypeOK ==
  /\ clr \in [CHAMS -> Colors]
  /\ mcnt \in [CHAMS -> Nat]
  /\ slot \in CHAMS \cup {Null}
  /\ meetings \in Nat
  /\ faded \subseteq CHAMS

NoOverLimit ==
  meetings <= N

SumInv ==
  Sum(mcnt, CHAMS) = 2 * meetings

AtLimitSafety ==
  (meetings = N) => (Sum(mcnt, CHAMS) = 2 * N)

=============================================================================