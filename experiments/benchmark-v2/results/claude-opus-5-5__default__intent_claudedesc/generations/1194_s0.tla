---- MODULE LargeInitialStateSpace ----
EXTENDS Naturals

CONSTANTS MaxX, MaxY, MaxZ

ASSUME /\ MaxX \in Nat
       /\ MaxY \in Nat
       /\ MaxZ \in Nat

\* Suggested model values for a meaningful benchmark:
\*   MaxX = 99, MaxY = 59, MaxZ = 39
\*   giving 100 * 60 * 40 = 240,000 distinct initial states.

VARIABLES x, y, z

vars == <<x, y, z>>

RangeX == 0..MaxX
RangeY == 0..MaxY
RangeZ == 0..MaxZ

TypeOK ==
    /\ x \in RangeX
    /\ y \in RangeY
    /\ z \in RangeZ

Init ==
    /\ x \in RangeX
    /\ y \in RangeY
    /\ z \in RangeZ

\* The system is purely static: no state ever changes.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Trivially true invariant.
Inv == TRUE

\* Every initial value stays the same forever.
StaysStatic == \A a \in RangeX, b \in RangeY, c \in RangeZ :
                  [](<<x, y, z>> = <<a, b, c>> => [](<<x, y, z>> = <<a, b, c>>))

THEOREM Spec => []Inv
THEOREM Spec => []TypeOK
====