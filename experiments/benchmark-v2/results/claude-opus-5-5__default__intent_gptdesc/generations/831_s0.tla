------------------------------ MODULE Elevator ------------------------------
(***************************************************************************)
(* A multi-car elevator system serving several people over a fixed set of  *)
(* floors. Environment actions (people choosing destinations and calling   *)
(* elevators) are kept separate from elevator actions (dispatching,        *)
(* moving, stopping, opening and closing doors, and accepting button       *)
(* presses). All actions interleave asynchronously. Fairness assumptions   *)
(* guarantee progress so that liveness properties can be checked.          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS   Person,     \* The set of all people using the elevator system
            Elevator,   \* The set of all elevators (cars)
            FloorCount  \* The number of floors served by the system

ASSUME FloorCount \in Nat /\ FloorCount >= 2
ASSUME Person /= {} /\ Elevator /= {}
ASSUME Person \cap Elevator = {}

VARIABLES   PersonState,            \* The state of each person
            ActiveElevatorCalls,    \* The set of all active elevator calls
            ElevatorState           \* The state of each elevator

Vars == <<PersonState, ActiveElevatorCalls, ElevatorState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Basic definitions                                                       *)
(***************************************************************************)
Floor == 1 .. FloorCount

Direction == {"Up", "Down"}

ElevatorCall == [floor : Floor, direction : Direction]

ElevatorDirectionState == Direction \cup {"Stationary"}

GetDistance[f1, f2 \in Floor] ==
    IF f1 > f2 THEN f1 - f2 ELSE f2 - f1

GetDirection[current, destination \in Floor] ==
    IF destination > current THEN "Up" ELSE "Down"

\* Whether elevator e is in position to immediately service call c
CanServiceCall[e \in Elevator, c \in ElevatorCall] ==
    /\ c.floor = ElevatorState[e].floor
    /\ c.direction = ElevatorState[e].direction

\* People waiting at floor f for an elevator going in direction d
PeopleWaiting[f \in Floor, d \in Direction] ==
    {p \in Person :
        /\ PersonState[p].location = f
        /\ PersonState[p].waiting
        /\ GetDirection[PersonState[p].location, PersonState[p].destination] = d}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type safety                                                             *)
(***************************************************************************)
TypeInvariant ==
    /\ PersonState \in [Person -> [location : Floor \cup Elevator,
                                   destination : Floor,
                                   waiting : BOOLEAN]]
    /\ ActiveElevatorCalls \subseteq ElevatorCall
    /\ ElevatorState \in [Elevator -> [floor : Floor,
                                       direction : ElevatorDirectionState,
                                       doorsOpen : BOOLEAN,
                                       buttonsPressed : SUBSET Floor]]

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
\* A button is pressed in a car only if some passenger inside wants that floor
ButtonsMatchPassengers ==
    \A e \in Elevator :
        \A f \in ElevatorState[e].buttonsPressed :
            \E p \in Person :
                /\ PersonState[p].location = e
                /\ PersonState[p].destination = f

\* Passengers are only carried in the direction of their destination
PassengersCarriedCorrectly ==
    \A p \in Person :
        \A e \in Elevator :
            (/\ PersonState[p].location = e
             /\ ElevatorState[e].floor /= PersonState[p].destination)
                => ElevatorState[e].direction =
                       GetDirection[ElevatorState[e].floor, PersonState[p].destination]

\* Every active call corresponds to actual waiting people
NoGhostCalls ==
    \A c \in ActiveElevatorCalls : PeopleWaiting[c.floor, c.direction] /= {}

SafetyInvariant ==
    /\ ButtonsMatchPassengers
    /\ PassengersCarriedCorrectly
    /\ NoGhostCalls

-----------------------------------------------------------------------------
(***************************************************************************)
(* Environment actions: people                                             *)
(***************************************************************************)
PickNewDestination(p) ==
    LET pState == PersonState[p] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ \E f \in Floor :
        /\ f /= pState.location
        /\ PersonState' = [PersonState EXCEPT ![p].destination = f]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CallElevator(p) ==
    LET pState == PersonState[p] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ pState.location /= pState.destination
    /\ LET call == [floor |-> pState.location,
                    direction |-> GetDirection[pState.location, pState.destination]]
       IN ActiveElevatorCalls' =
            IF \E e \in Elevator :
                    /\ CanServiceCall[e, call]
                    /\ ElevatorState[e].doorsOpen
            THEN ActiveElevatorCalls
            ELSE ActiveElevatorCalls \cup {call}
    /\ PersonState' = [PersonState EXCEPT ![p].waiting = TRUE]
    /\ UNCHANGED <<ElevatorState>>

EnvironmentNext ==
    \/ \E p \in Person : PickNewDestination(p)
    \/ \E p \in Person : CallElevator(p)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Elevator actions                                                        *)
(***************************************************************************)
OpenElevatorDoors(e) ==
    LET eState == ElevatorState[e] IN
    /\ ~eState.doorsOpen
    /\ \/ \E call \in ActiveElevatorCalls : CanServiceCall[e, call]
       \/ eState.floor \in eState.buttonsPressed
    /\ ElevatorState' = [ElevatorState EXCEPT
                            ![e].doorsOpen = TRUE,
                            ![e].buttonsPressed = @ \ {eState.floor}]
    /\ ActiveElevatorCalls' =
            ActiveElevatorCalls \ {[floor |-> eState.floor,
                                    direction |-> eState.direction]}
    /\ UNCHANGED <<PersonState>>

\* Waiting people going the car's way board and press their destination buttons
EnterElevator(e) ==
    LET eState == ElevatorState[e] IN
    /\ eState.doorsOpen
    /\ eState.direction /= "Stationary"
    /\ LET gettingOn == PeopleWaiting[eState.floor, eState.direction]
           destinations == {PersonState[p].destination : p \in gettingOn}
       IN /\ gettingOn /= {}
          /\ PersonState' = [p \in Person |->
                IF p \in gettingOn
                THEN [PersonState[p] EXCEPT !.location = e]
                ELSE PersonState[p]]
          /\ ElevatorState' = [ElevatorState EXCEPT
                                  ![e].buttonsPressed = @ \cup destinations]
    /\ UNCHANGED <<ActiveElevatorCalls>>

ExitElevator(e) ==
    LET eState == ElevatorState[e] IN
    /\ eState.doorsOpen
    /\ LET gettingOff == {p \in Person :
                            /\ PersonState[p].location = e
                            /\ PersonState[p].destination = eState.floor}
       IN /\ gettingOff /= {}
          /\ PersonState' = [p \in Person |->
                IF p \in gettingOff
                THEN [PersonState[p] EXCEPT !.location = eState.floor,
                                            !.waiting = FALSE]
                ELSE PersonState[p]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CloseElevatorDoors(e) ==
    /\ ElevatorState[e].doorsOpen
    /\ ~ENABLED EnterElevator(e)
    /\ ~ENABLED ExitElevator(e)
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].doorsOpen = FALSE]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

MoveElevator(e) ==
    LET eState == ElevatorState[e]
        nextFloor == IF eState.direction = "Up"
                     THEN eState.floor + 1
                     ELSE eState.floor - 1
    IN
    /\ eState.direction /= "Stationary"
    /\ ~eState.doorsOpen
    /\ eState.floor \notin eState.buttonsPressed
    /\ \A call \in ActiveElevatorCalls :
            CanServiceCall[e, call] =>
                \E e2 \in Elevator : e /= e2 /\ CanServiceCall[e2, call]
    /\ nextFloor \in Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].floor = nextFloor]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

StopElevator(e) ==
    LET eState == ElevatorState[e]
        nextFloor == IF eState.direction = "Up"
                     THEN eState.floor + 1
                     ELSE eState.floor - 1
    IN
    /\ eState.direction /= "Stationary"
    /\ ~ENABLED OpenElevatorDoors(e)
    /\ ~eState.doorsOpen
    /\ nextFloor \notin Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].direction = "Stationary"]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

(***************************************************************************)
(* Dispatch policy: candidates are cars that are stationary or already     *)
(* approaching the call floor in the call's direction. The policy picks    *)
(* a closest candidate. Any other policy selecting from Candidates(c) can  *)
(* be substituted for DispatchPolicy without changing the rest of the spec.*)
(***************************************************************************)
Stationary == {e \in Elevator : ElevatorState[e].direction = "Stationary"}

Approaching(c) ==
    {e \in Elevator :
        /\ ElevatorState[e].direction = c.direction
        /\ \/ ElevatorState[e].floor = c.floor
           \/ GetDirection[ElevatorState[e].floor, c.floor] = c.direction}

Candidates(c) == Stationary \cup Approaching(c)

DispatchPolicy(c) ==
    CHOOSE e \in Candidates(c) :
        \A e2 \in Candidates(c) :
            GetDistance[ElevatorState[e].floor, c.floor]
                <= GetDistance[ElevatorState[e2].floor, c.floor]

DispatchElevator(c) ==
    /\ c \in ActiveElevatorCalls
    /\ Candidates(c) /= {}
    /\ LET chosen == DispatchPolicy(c) IN
       ElevatorState' =
            IF chosen \in Stationary
            THEN [ElevatorState EXCEPT ![chosen].floor = c.floor,
                                       ![chosen].direction = c.direction]
            ELSE ElevatorState
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

ElevatorNext ==
    \/ \E e \in Elevator : OpenElevatorDoors(e)
    \/ \E e \in Elevator : EnterElevator(e)
    \/ \E e \in Elevator : ExitElevator(e)
    \/ \E e \in Elevator : CloseElevatorDoors(e)
    \/ \E e \in Elevator : MoveElevator(e)
    \/ \E e \in Elevator : StopElevator(e)
    \/ \E c \in ElevatorCall : DispatchElevator(c)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Init ==
    /\ PersonState \in [Person -> [location : Floor,
                                   destination : Floor,
                                   waiting : {FALSE}]]
    /\ ActiveElevatorCalls = {}
    /\ ElevatorState \in [Elevator -> [floor : Floor,
                                       direction : {"Stationary"},
                                       doorsOpen : {FALSE},
                                       buttonsPressed : {{}}]]

Next == EnvironmentNext \/ ElevatorNext

Fairness ==
    /\ \A p \in Person : WF_Vars(CallElevator(p))
    /\ \A e \in Elevator : WF_Vars(OpenElevatorDoors(e))
    /\ \A e \in Elevator : WF_Vars(EnterElevator(e))
    /\ \A e \in Elevator : WF_Vars(ExitElevator(e))
    /\ \A e \in Elevator : SF_Vars(CloseElevatorDoors(e))
    /\ \A e \in Elevator : SF_Vars(MoveElevator(e))
    /\ \A e \in Elevator : WF_Vars(StopElevator(e))
    /\ \A c \in ElevatorCall : SF_Vars(DispatchElevator(c))

Spec == Init /\ [][Next]_Vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness and progress properties                                        *)
(***************************************************************************)
\* Every active call is eventually serviced by a car at that floor with open doors
CallsEventuallyServiced ==
    \A c \in ElevatorCall :
        c \in ActiveElevatorCalls ~>
            \E e \in Elevator :
                /\ ElevatorState[e].floor = c.floor
                /\ (CanServiceCall[e, c] \/ ElevatorState[e].doorsOpen)

\* Every active call is eventually in a position to be serviced
CallsEventuallyReached ==
    \A c \in ElevatorCall :
        c \in ActiveElevatorCalls ~> \E e \in Elevator : CanServiceCall[e, c]

\* Every waiting person eventually reaches their destination
PeopleEventuallyArrive ==
    \A p \in Person :
        PersonState[p].waiting ~>
            PersonState[p].location = PersonState[p].destination

Liveness ==
    /\ CallsEventuallyReached
    /\ CallsEventuallyServiced
    /\ PeopleEventuallyArrive

\* No deadlock: some action is always enabled
NoDeadlock == [](ENABLED Next)

\* Cars able to open, move, or close eventually do something
ElevatorProgress ==
    \A e \in Elevator :
        /\ []<>(ENABLED OpenElevatorDoors(e)) => []<><<OpenElevatorDoors(e)>>_Vars
        /\ ElevatorState[e].doorsOpen ~> ~ElevatorState[e].doorsOpen

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant)
THEOREM Spec => Liveness
THEOREM Spec => NoDeadlock
=============================================================================