---- MODULE Coverage ----
EXTENDS Naturals

VARIABLES x, y

c == x
d == y

vars == <<x, y>>

Init == /\ x \in 1..3
        /\ y = 0

A == /\ x' = x + 1
     /\ y' = y

B == /\ x \in Nat
     /\ UNCHANGED vars

B2 == /\ x \in Nat
      /\ UNCHANGED vars

C == /\ x = 42
     /\ x' = TRUE
     /\ y' = FALSE

U1 == /\ x < 0
      /\ UNCHANGED vars

U2 == /\ x < 0
      /\ x' = x + 1
      /\ y' = y

U3 == /\ x < 0
      /\ UNCHANGED <<c, d>>

U4 == /\ x < 0
      /\ x' = x - 1
      /\ y' = y + 1

UC1 == /\ x \in Nat
       /\ UNCHANGED vars

UC2 == /\ x \in Nat
       /\ UNCHANGED <<x, y>>

UC3 == /\ x \in Nat
       /\ UNCHANGED <<c, d>>

Next == \/ A
        \/ B
        \/ B2
        \/ C
        \/ U1
        \/ U2
        \/ U3
        \/ U4
        \/ UC1
        \/ UC2
        \/ UC3

Spec == Init /\ [][Next]_vars

Constraint == x < 20

====