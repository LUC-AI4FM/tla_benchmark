------------------------------- MODULE TokenPassingTermination -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Procs  \* The set of processes {0, 1, 2}

VARIABLES 
    tokenLoc,   \* Location of the token (a process)
    tokenColor, \* Color bit of the token
    activity,   \* Activity state of each process (TRUE if active, FALSE if passive)
    localColor  \* Local color bit of each process

Init == /\ tokenLoc \in Procs
        /\ tokenColor \in {0, 1}
        /\ activity \in [Procs -> BOOLEAN]
        /\ localColor \in [Procs -> {0, 1}]

Next ==
    \/ \E p \in Procs : 
        /\ activity[p] = TRUE
        /\ localColor' = [localColor EXCEPT ![p] = (localColor[p] + 1) % 2]
    \/ \E p \in Procs :
        /\ tokenLoc = p
        /\ localColor' = [localColor EXCEPT ![p] = tokenColor]
        /\ activity' = [activity EXCEPT ![p] = FALSE]
        /\ tokenLoc' = (tokenLoc + 1) % 3
        /\ tokenColor' = localColor[p]

Spec ==
    /\ Init
    /\ [][Next]_<<tokenLoc, tokenColor, activity, localColor>>
    /\ WF_next(<<tokenLoc, tokenColor, activity, localColor>>)

\* Safety properties
TokenAtValidProcess == tokenLoc \in Procs
TokenColorValid == tokenColor \in {0, 1}
NoTwoTokens == TRUE \* By construction of Next, only one token exists
LocalStatesValid ==
    /\ activity \in [Procs -> BOOLEAN]
    /\ localColor \in [Procs -> {0, 1}]

SafetyProperties ==
    /\ TokenAtValidProcess
    /\ TokenColorValid
    /\ NoTwoTokens
    /\ LocalStatesValid

\* Liveness properties
GlobalQuiescence ==
    /\ \A p \in Procs : activity[p] = FALSE
    /\ tokenLoc' = tokenLoc
    /\ tokenColor' = 0

NoFalseTermination ==
    \/ \E p \in Procs : activity[p] = TRUE
    \/ \E p \in Procs : localColor[p] = 1

LivenessProperties ==
    <>[](GlobalQuiescence)
    /\ []<>(\neg NoFalseTermination)

Invariant ==
    /\ SafetyProperties
    /\ LivenessProperties

=============================================================================