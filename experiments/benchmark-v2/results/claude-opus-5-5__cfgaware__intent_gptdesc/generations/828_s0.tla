---------------------------- MODULE BoxSearch ----------------------------
EXTENDS Naturals

CONSTANT Number_Of_Boxes

ASSUME Number_Of_Boxes \in Nat /\ Number_Of_Boxes >= 1

VARIABLES pos, lastObserved, orientation, objectBox, found, justInspected

vars == <<pos, lastObserved, orientation, objectBox, found, justInspected>>

Boxes        == 1..Number_Of_Boxes
NoBox        == 0
Orientations == {"left", "right"}

TypeOK ==
    /\ pos \in Boxes
    /\ lastObserved \in Boxes \cup {NoBox}
    /\ orientation \in Orientations
    /\ objectBox \in Boxes
    /\ found \in BOOLEAN
    /\ justInspected \in BOOLEAN

Init ==
    /\ pos \in Boxes
    /\ lastObserved = NoBox
    /\ orientation \in Orientations
    /\ objectBox \in Boxes
    /\ found = FALSE
    /\ justInspected = FALSE

MoveLeft ==
    /\ pos > 1
    /\ pos' = pos - 1
    /\ justInspected' = FALSE
    /\ UNCHANGED <<lastObserved, orientation, objectBox, found>>

MoveRight ==
    /\ pos < Number_Of_Boxes
    /\ pos' = pos + 1
    /\ justInspected' = FALSE
    /\ UNCHANGED <<lastObserved, orientation, objectBox, found>>

MoveForward ==
    \/ /\ orientation = "left"
       /\ MoveLeft
    \/ /\ orientation = "right"
       /\ MoveRight

Inspect ==
    /\ lastObserved' = pos
    /\ found' = (found \/ (pos = objectBox))
    /\ justInspected' = TRUE
    /\ UNCHANGED <<pos, orientation, objectBox>>

FlipOrientation ==
    /\ orientation' = IF orientation = "left" THEN "right" ELSE "left"
    /\ justInspected' = FALSE
    /\ UNCHANGED <<pos, lastObserved, objectBox, found>>

SetOrientation ==
    /\ \E o \in Orientations : orientation' = o
    /\ justInspected' = FALSE
    /\ UNCHANGED <<pos, lastObserved, objectBox, found>>

Next ==
    \/ MoveLeft
    \/ MoveRight
    \/ MoveForward
    \/ Inspect
    \/ FlipOrientation
    \/ SetOrientation

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* A fair search strategy: the agent keeps moving forward, keeps flipping
\* when blocked, and inspects boxes infinitely often.
FairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(MoveForward)
    /\ WF_vars(FlipOrientation)
    /\ SF_vars(Inspect /\ pos = objectBox)

-----------------------------------------------------------------------------
\* Safety properties

LastObservedValid == lastObserved \in Boxes \cup {NoBox}

InspectRecordsPosition == justInspected => lastObserved = pos

OrientationValid == orientation \in Orientations

PositionInBounds == pos \in Boxes

FoundCorrect == found => (lastObserved = objectBox \/ objectBox \in Boxes)

Safety ==
    /\ TypeOK
    /\ LastObservedValid
    /\ InspectRecordsPosition
    /\ OrientationValid
    /\ PositionInBounds

InspectStep == [][Inspect => lastObserved' = pos]_vars

MovesInBounds == [][pos' \in Boxes /\ (pos' = pos \/ pos' = pos + 1 \/ pos' = pos - 1)]_vars

NoDeadlock == ENABLED Next

-----------------------------------------------------------------------------
\* Liveness properties

EventuallyInspectObject == <>(lastObserved = objectBox)

EventuallyFound == <>found

=============================================================================