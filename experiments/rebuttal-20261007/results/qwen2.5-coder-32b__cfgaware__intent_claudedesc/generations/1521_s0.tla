------------------------------- MODULE CoffeeCan --------------------------------

CONSTANTS MaxBeans \* The maximum number of beans in the can

VARIABLES white, black \* Counts of white and black beans

Init == /\ white \in 0..MaxBeans
        /\ black \in 0..MaxBeans
        /\ white + black > 0

Next ==
    \/ /\ white >= 2
       /\ \/ /\ white' = white - 1
              /\ black' = black + 1
          \/ /\ white' = white - 2
             /\ black' = black + 1
    \/ /\ black >= 2
       /\ \/ /\ white' = white + 1
              /\ black' = black - 1
          \/ /\ white' = white
             /\ black' = black - 2
    \/ /\ white > 0
       /\ /\ black > 0
          /\ white' = white - 1
          /\ black' = black

Spec == Init /\ [][Next]_<<white, black>>

Termination ==
    \A s \in StateSpace: <s>_(\E t \in StateSpace: (white + black)' = 1)

ParityInvariant ==
    \A s \in StateSpace: white % 2 = [][Next]_<<white>>[s]

FinalColor ==
    \A s \in StateSpace:
        /\ (white % 2 = 0) => <s>_(\E t \in StateSpace: black' = 1)
        /\ (white % 2 = 1) => <s>_(\E t \in StateSpace: white' = 1)

StateSpace == { <<w, b>> \in [0..MaxBeans] \X [0..MaxBeans] : w + b > 0 }

Fairness ==
    WF_next(<<white, black>>, Next)

THEOREM Spec => []Termination
THEOREM Spec => []ParityInvariant
THEOREM Spec => []FinalColor

=============================================================================