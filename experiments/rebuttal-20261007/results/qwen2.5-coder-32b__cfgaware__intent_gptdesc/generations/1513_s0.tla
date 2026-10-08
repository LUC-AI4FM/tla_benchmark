------------------------------- MODULE TokenPassingTermination -------------------------------

CONSTANTS 
    \* Constants for processes, colors, and initial states
    ProcSet == {P1, P2, P3},
    Colors == {BLACK, WHITE}

VARIABLES 
    \* Variables to track the state of each process and the token
    activity,  \* Maps each process to its activity status (TRUE for active, FALSE for passive)
    localColor, \* Maps each process to its local color bit
    tokenHolder, \* The current holder of the token
    tokenColor   \* The color of the token

ASSUME 
    \* Initial conditions: all processes are initially passive and have a default local color
    Init == /\ activity = [p \in ProcSet |-> FALSE]
            /\ localColor = [p \in ProcSet |-> BLACK]
            /\ tokenHolder \in ProcSet
            /\ tokenColor \in Colors

\* Next-state relation for the system
Next ==
    \/ \E p \in ProcSet : GenerateWork(p)
    \/ \E p \in ProcSet : ChangeLocalActivity(p)
    \/ \E p \in ProcSet : ChangeLocalColor(p)
    \/ ForwardToken

GenerateWork(p) ==
    /\ activity[p]
    /\ localColor' = [localColor EXCEPT ![p] = WHITE]
    /\ UNCHANGED <<activity, tokenHolder, tokenColor>>

ChangeLocalActivity(p) ==
    /\ UNCHANGED localColor
    /\ activity' = [activity EXCEPT ![p] = ~activity[p]]
    /\ UNCHANGED <<tokenHolder, tokenColor>>

ChangeLocalColor(p) ==
    /\ activity[p]
    /\ localColor' = [localColor EXCEPT ![p] = (IF localColor[p] = BLACK THEN WHITE ELSE BLACK)]
    /\ UNCHANGED <<activity, tokenHolder, tokenColor>>

ForwardToken ==
    /\ \E p \in ProcSet : tokenHolder = p
    /\ LET nextProc == CHOOSE q \in ProcSet : q # p
       IN  /\ tokenHolder' = nextProc
           /\ tokenColor' = (IF localColor[tokenHolder] = WHITE THEN WHITE ELSE BLACK)
           /\ UNCHANGED <<activity, localColor>>

\* Specification of the system behavior
Spec ==
    Init /\ [][Next]_<<activity, localColor, tokenHolder, tokenColor>>

\* Safety properties
Safety ==
    /\ \A p \in ProcSet : activity[p] \in {TRUE, FALSE}
    /\ \A p \in ProcSet : localColor[p] \in Colors
    /\ tokenHolder \in ProcSet
    /\ tokenColor \in Colors

\* Liveness property for termination detection
Termination ==
    <>[](\A p \in ProcSet : ~activity[p] /\ localColor[p] = BLACK) => <><>(tokenHolder' = tokenHolder)

\* Fairness assumptions
WF_ST == WF_next(Next, <<activity, localColor, tokenHolder, tokenColor>>)
SF_ST == SF_next(Next, <<activity, localColor, tokenHolder, tokenColor>>)

\* Complete specification with fairness
CompleteSpec ==
    Spec /\ Safety /\ Termination /\ WF_ST /\ SF_ST

=============================================================================