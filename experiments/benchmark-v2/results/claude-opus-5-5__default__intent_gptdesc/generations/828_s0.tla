------------------------------ MODULE BoxSearch ------------------------------
(***************************************************************************)
(* An agent searches a line of boxes for an object. It can move between   *)
(* adjacent boxes, inspect the current box (recording it as the last box  *)
(* observed), and flip or set its orientation. Moves, inspections and     *)
(* orientation changes are chosen nondeterministically, so different      *)
(* search strategies can be explored.                                     *)
(*                                                                         *)
(* Spec      : fully nondeterministic agent, no progress guarantee.       *)
(* SweepSpec : one concrete strategy (a boustrophedon sweep) under weak   *)
(*             fairness. It shows that the model allows the agent to      *)
(*             eventually inspect the box holding the object.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N                       \* number of boxes

ASSUME NAssumption == N \in Nat /\ N >= 1

Boxes        == 1..N
NoBox        == 0                \* sentinel: "no box"
Orientations == {"left", "right"}
ActionTags   == {"init", "move", "inspect", "turn"}

VARIABLES
    pos,         \* box the agent currently occupies
    lastSeen,    \* last box inspected, or NoBox
    orient,      \* current orientation of the agent
    objectAt,    \* box containing the object, or NoBox (fixed for a run)
    visited,     \* set of boxes inspected so far
    found,       \* TRUE once the agent has inspected the object's box
    lastAction   \* tag of the most recent step (used for observation)

vars == <<pos, lastSeen, orient, objectAt, visited, found, lastAction>>

---------------------------------------------------------------------------
(* Initial conditions *)

Init ==
    /\ pos        \in Boxes
    /\ lastSeen   =  NoBox
    /\ orient     \in Orientations
    /\ objectAt   \in Boxes \cup {NoBox}
    /\ visited    =  {}
    /\ found      =  FALSE
    /\ lastAction =  "init"

---------------------------------------------------------------------------
(* Actions *)

MoveLeft ==
    /\ pos > 1
    /\ pos' = pos - 1
    /\ lastAction' = "move"
    /\ UNCHANGED <<lastSeen, orient, objectAt, visited, found>>

MoveRight ==
    /\ pos < N
    /\ pos' = pos + 1
    /\ lastAction' = "move"
    /\ UNCHANGED <<lastSeen, orient, objectAt, visited, found>>

Move == MoveLeft \/ MoveRight

Inspect ==
    /\ lastSeen'   = pos
    /\ visited'    = visited \cup {pos}
    /\ found'      = (found \/ pos = objectAt)
    /\ lastAction' = "inspect"
    /\ UNCHANGED <<pos, orient, objectAt>>

Flip ==
    /\ orient' = IF orient = "left" THEN "right" ELSE "left"
    /\ lastAction' = "turn"
    /\ UNCHANGED <<pos, lastSeen, objectAt, visited, found>>

SetOrientation(o) ==
    /\ o \in Orientations
    /\ orient' = o
    /\ lastAction' = "turn"
    /\ UNCHANGED <<pos, lastSeen, objectAt, visited, found>>

Next ==
    \/ Move
    \/ Inspect
    \/ Flip
    \/ \E o \in Orientations : SetOrientation(o)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* A concrete search strategy: inspect the current box if it has not been *)
(* inspected yet; otherwise move in the current orientation; at a         *)
(* boundary, flip. Every step is also a Next step.                        *)

SweepStep ==
    \/ /\ pos \notin visited
       /\ Inspect
    \/ /\ pos \in visited
       /\ orient = "right" /\ pos < N
       /\ MoveRight
    \/ /\ pos \in visited
       /\ orient = "left" /\ pos > 1
       /\ MoveLeft
    \/ /\ pos \in visited
       /\ \/ orient = "right" /\ pos = N
          \/ orient = "left"  /\ pos = 1
       /\ Flip

SweepSpec == Init /\ [][SweepStep]_vars /\ WF_vars(SweepStep)

(* Spec with fairness on the strategy embedded as a sub-action of Next *)
FairSpec == Spec /\ SF_vars(SweepStep)

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ pos        \in Boxes
    /\ lastSeen   \in Boxes \cup {NoBox}
    /\ orient     \in Orientations
    /\ objectAt   \in Boxes \cup {NoBox}
    /\ visited    \subseteq Boxes
    /\ found      \in BOOLEAN
    /\ lastAction \in ActionTags

\* Last observed box is always a valid index or the sentinel
LastSeenValid == lastSeen \in Boxes \cup {NoBox}

\* Immediately after an inspection, last observed equals the position
InspectRecordsPosition == (lastAction = "inspect") => (lastSeen = pos)

\* The same requirement, stated as an action property
InspectActionProperty == [][Inspect => lastSeen' = pos']_vars

\* Orientation is always one of the allowed values
OrientationValid == orient \in Orientations

\* The agent never leaves the bounds of the box array
PositionInBounds == pos \in 1..N

\* Every move goes to an adjacent box inside the bounds
MoveStepsValid ==
    [][ (pos' # pos) => (pos' \in Boxes /\ (pos' = pos + 1 \/ pos' = pos - 1)) ]_vars

\* found is TRUE exactly when the object's box has been inspected
FoundConsistent == found <=> (objectAt \in visited)

\* The last observed box is one that was actually inspected
LastSeenVisited == (lastSeen # NoBox) => (lastSeen \in visited)

\* Absence of deadlock: some action is always enabled
DeadlockFree == ENABLED Next

SafetyInvariant ==
    /\ TypeOK
    /\ LastSeenValid
    /\ InspectRecordsPosition
    /\ OrientationValid
    /\ PositionInBounds
    /\ FoundConsistent
    /\ LastSeenVisited
    /\ DeadlockFree

---------------------------------------------------------------------------
(* Liveness properties (hold under SweepSpec) *)

\* If the object is in some box, the agent eventually inspects that box
EventuallyInspectsObjectBox ==
    (objectAt \in Boxes) => <>(lastSeen = objectAt)

\* If the object is in some box, it is eventually found, and stays found
EventuallyFound ==
    (objectAt \in Boxes) => <>[]found

\* Every box is eventually inspected
EventuallyAllVisited == <>(visited = Boxes)

\* The agent always keeps acting (no permanent stuttering)
AlwaysProgress == []<><<Next>>_vars

THEOREM Spec => []SafetyInvariant
THEOREM SweepSpec => []SafetyInvariant
THEOREM SweepSpec => EventuallyInspectsObjectBox /\ EventuallyFound
                     /\ EventuallyAllVisited
=============================================================================