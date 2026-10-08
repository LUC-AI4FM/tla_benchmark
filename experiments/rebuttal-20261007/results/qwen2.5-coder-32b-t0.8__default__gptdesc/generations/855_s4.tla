------------------------------- MODULE PrisonersAndSwitches ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Prisoners \* The set of all prisoners
VARIABLES
    counter, \* The designated prisoner who acts as a counter
    switchA, \* Boolean representing the state of switch A (TRUE = up, FALSE = down)
    switchB, \* Boolean representing the state of switch B (TRUE = up, FALSE = down)
    visits   \* Set of prisoners who have visited the room

Init == /\ counter \in Prisoners
        /\ switchA = FALSE
        /\ switchB = FALSE
        /\ visits = {}

Next ==
    LET chosenPrisoner \in Prisoners
    IN \/ \/ chosenPrisoner = counter
           /\ \/ /\ switchA
                  /\ switchA' = FALSE
                  /\ switchB' = switchB
                  /\ visits' = visits \cup {chosenPrisoner}
                  /\ IF Cardinality(visits) + 1 = Cardinality(Prisoners)
                     THEN UNCHANGED \<<switchA, switchB>>
                     ELSE visits' = visits \cup {chosenPrisoner}
           \/ /\ NOT switchA
                  /\ switchA' = switchA
                  /\ switchB' = NOT switchB
                  /\ visits' = visits
       \/ chosenPrisoner # counter
          /\ (/\ switchA
                 /\ visits' = visits \cup {chosenPrisoner}
                 /\ IF Cardinality(visits) + 1 = Cardinality(Prisoners)
                    THEN UNCHANGED \<<switchA, switchB>>
                    ELSE visits' = visits \cup {chosenPrisoner}
             \/ NOT switchA
                /\ switchA' = switchA
                /\ switchB' = NOT switchB
                /\ visits' = visits)

Spec ==
    WF_vars(Next) /\
    SF_vars(Init, Next) /\
    [](visits = Prisoners => UNCHANGED \<<switchA, switchB, visits>>) \/
       (/\ visits # Prisoners
        /\ \/ switchA
           /\ switchA' = FALSE
           /\ switchB' = switchB
           /\ visits' = visits \cup {counter}
        \/ NOT switchA
           /\ switchA' = switchA
           /\ switchB' = NOT switchB
           /\ visits' = visits)

Safety == [](visits = Prisoners => UNCHANGED \<<switchA, switchB, visits>>)

Liveness ==
    <>(/\ switchA
        /\ Cardinality(visits) + 1 = Cardinality(Prisoners))

=============================================================================