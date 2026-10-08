------------------------------- MODULE PlusCalAlgorithm -------------------------------

EXTENDS Integers, TLC, PCal

CONSTANTS InitX \* x is initially chosen from the integer range 1..10

VARIABLES x, pc

Init == 
    /\ x = InitX
    /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x ^ 2 <= 100
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ pc' = pc
       /\ x' = x

Spec == 
    /\ Init
    /\ [][Next]_<<pc, x>>
    /\ WF_next(<<pc, x>>)

Termination ==
    <>[](pc = "Done")

=============================================================================