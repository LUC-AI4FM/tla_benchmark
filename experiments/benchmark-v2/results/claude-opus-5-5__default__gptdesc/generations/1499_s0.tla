module CoverageStatistics

EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

c == x

d == x'

a == y'

Init == /\ x = 0
        /\ y = 0

A == /\ x' = x + 1
     /\ y' = y

B == /\ x' = c + 1
     /\ UNCHANGED y

C == /\ d = x + 1
     /\ a = y

D == /\ x < 5
     /\ x' = x + 1
     /\ UNCHANGED <<y>>

E == /\ y < 5
     /\ y' = y + 1
     /\ UNCHANGED x

F == /\ x > 0
     /\ x' = x - 1
     /\ y' = y

G == /\ UNCHANGED <<x, y>>

H == /\ UNCHANGED vars

Next == \/ A
        \/ B
        \/ C
        \/ D
        \/ E
        \/ F
        \/ G
        \/ H

Spec == Init /\ [][Next]_vars

Op1(S) == \A T \in SUBSET S : Cardinality(T) <= Cardinality(S)

Op2(n) == \E T \in SUBSET (1..n) : Cardinality(T) = n

Inv == /\ x \in Nat
       /\ y \in Nat
       /\ Op1(1..3)

Inv2 == /\ Op2(3)
        /\ \A T \in SUBSET (0..2) : Cardinality(T) >= 0

====