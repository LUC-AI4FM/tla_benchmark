------------------------------- MODULE ProcIncrement -------------------------------
EXTENDS Integers, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x, pcA, pcB

Init == 
    /\ x = 0
    /\ pcA = "start"
    /\ pcB = "start"

Next ==
    \/ /\ pcA = "start"
       /\ x' = x + 1
       /\ pcA' = "Done"
       /\ UNCHANGED <<pcB>>
    \/ /\ pcB = "start"
       /\ x' = x + 1
       /\ pcB' = "Done"
       /\ UNCHANGED <<pcA>>
    \/ Terminating

Terminating ==
    /\ pcA = "Done"
    /\ pcB = "Done"
    /\ x' = x
    /\ UNCHANGED <<pcA, pcB>>

Spec == 
    Init /\ [][Next]_<<x, pcA, pcB>> /\ <><Terminating>_<<x, pcA, pcB>>

\* Safety properties
TypeOK ==
    /\ x \in Int
    /\ pcA \in {"start", "Done"}
    /\ pcB \in {"start", "Done"}

MutualExclusion ==
    \/ pcA = "start"
    \/ pcB = "start"
    \/ Terminating

\* Liveness properties
Termination ==
    <><pcA = "Done" /\ pcB = "Done">_<<x, pcA, pcB>>

Fairness ==
    WF_[Next]_<<pcA>> /\ SF_[Next]_<<pcA>>
    /\ WF_[Next]_<<pcB>> /\ SF_[Next]_<<pcB>>

CompleteSpec == Spec /\ TypeOK /\ MutualExclusion /\ Termination /\ Fairness
================================================================================