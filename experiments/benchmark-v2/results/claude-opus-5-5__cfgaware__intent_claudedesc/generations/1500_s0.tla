---- MODULE CoverageStatistics ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the underlying variables
a == x
b == y

Init == /\ x \in 1..3
        /\ y = 0

\* Reachable actions using aliased variables
A == /\ y' = b + 1
     /\ x' = a

\* Reachable actions with different UNCHANGED syntax
B == /\ y' = y + 1
     /\ UNCHANGED x

C == /\ y' = y + 1
     /\ UNCHANGED <<x>>

\* Unreachable actions (impossible guards)
U1 == /\ x < 0
      /\ y' = y + 1
      /\ x' = x

U2 == /\ y < 0
      /\ UNCHANGED vars

U3 == /\ x < 0
      /\ UNCHANGED <<x, y>>

U4 == /\ y < 0
      /\ UNCHANGED x
      /\ UNCHANGED y

U5 == /\ x < 0
      /\ UNCHANGED <<a, b>>

\* Reachable but trivial (stuttering) actions
D == UNCHANGED vars

E == /\ UNCHANGED x
     /\ UNCHANGED y

F == UNCHANGED <<x, y>>

Next == \/ A
        \/ B
        \/ C
        \/ U1
        \/ U2
        \/ U3
        \/ U4
        \/ U5
        \/ D
        \/ E
        \/ F

Spec == Init /\ [][Next]_vars

Constraint == y < 3

====