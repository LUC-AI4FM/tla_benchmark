------------------------------- MODULE DieHard -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* Constants for jug capacities
    J3_CAPACITY,
    J5_CAPACITY

VARIABLES 
    \* Variables to track the amount of water in each jug and total gallons drawn from the fountain
    j3, 
    j5, 
    totalGallonsDrawn

Init == /\ j3 = 0
        /\ j5 = 0
        /\ totalGallonsDrawn = 0

\* Actions to fill either jug to capacity
FillJ3 == /\ j3' < J3_CAPACITY
          /\ j3' = J3_CAPACITY
          /\ j5' = j5
          /\ totalGallonsDrawn' = totalGallonsDrawn + (J3_CAPACITY - j3)

FillJ5 == /\ j5' < J5_CAPACITY
          /\ j5' = J5_CAPACITY
          /\ j3' = j3
          /\ totalGallonsDrawn' = totalGallonsDrawn + (J5_CAPACITY - j5)

\* Actions to empty either jug completely
EmptyJ3 == /\ j3' = 0
           /\ j5' = j5
           /\ totalGallonsDrawn' = totalGallonsDrawn

EmptyJ5 == /\ j5' = 0
           /\ j3' = j3
           /\ totalGallonsDrawn' = totalGallonsDrawn

\* Actions to pour water from one jug into the other
PourJ3toJ5 == /\ j5 + j3 <= J5_CAPACITY
              /\ j5' = j5 + j3
              /\ j3' = 0
              /\ totalGallonsDrawn' = totalGallonsDrawn

PourJ5toJ3 == /\ j3 + j5 <= J3_CAPACITY
              /\ j3' = j3 + j5
              /\ j5' = 0
              /\ totalGallonsDrawn' = totalGallonsDrawn

\* General pour actions that stop when the source is empty or the destination is full
PourJ3toJ5General == /\ j5' <= J5_CAPACITY
                     /\ j5' = Min(j5 + j3, J5_CAPACITY)
                     /\ j3' = j3 - (j5' - j5)
                     /\ totalGallonsDrawn' = totalGallonsDrawn

PourJ5toJ3General == /\ j3' <= J3_CAPACITY
                     /\ j3' = Min(j3 + j5, J3_CAPACITY)
                     /\ j5' = j5 - (j3' - j3)
                     /\ totalGallonsDrawn' = totalGallonsDrawn

Next == \/ FillJ3
        \/ FillJ5
        \/ EmptyJ3
        \/ EmptyJ5
        \/ PourJ3toJ5General
        \/ PourJ5toJ3General

Spec == Init /\ [][Next]_<<j3, j5, totalGallonsDrawn>>

\* Type invariants
TypeInvariant == /\ j3 \in 0..J3_CAPACITY
                 /\ j5 \in 0..J5_CAPACITY
                 /\ totalGallonsDrawn \in Nat

\* Safety properties
Safety == TypeInvariant

\* Liveness property to verify that the big jug can reach exactly 4 gallons
Liveness == <>(j5 = 4)

\* Fairness conditions
Fairness == WF_vars(Next, <<j3, j5>>)

THEOREM Spec => []Safety /\ <>Liveness /\ Fairness

=============================================================================