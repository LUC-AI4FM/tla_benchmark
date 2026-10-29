------------------------------ MODULE Elevator ------------------------------
(***************************************************************************)
(* A simple multi-car elevator system. People choose destinations, call   *)
(* elevators, enter and exit cars. Elevators open and close doors, move,  *)
(* stop, and are dispatched to calls using a simple nearest-eligible      *)
(* elevator policy.                                                       *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    Person,      \* The set of all people using the elevator system
    Elevator,    \* The set of all elevators
    FloorCount   \* The number of floors serviced by the elevator system

ASSUME FloorCount \in Nat \ {0}
ASSUME Person /= {} /\ Elevator /= {}
ASSUME Elevator \cap (1 .. FloorCount) = {}

VARIABLES
    PersonState,          \* The state of each person
    ActiveElevatorCalls,  \* The set of active elevator calls
    ElevatorState         \* The state of each elevator

Vars == <<PersonState, ActiveElevatorCalls, ElevatorState>>

Floor == 1 .. FloorCount

Direction == {"Up", "Down"}

ElevatorCall == [floor : Floor, direction : Direction]

ElevatorDirectionState == Direction \cup {"Stationary"}

GetDistance[f1, f2 \in Floor] ==
    IF f1 > f2 THEN f1 - f2 ELSE f2 - f1

GetDirection[current, destination \in Floor] ==
    IF destination > current THEN "Up" ELSE "Down"

CanServiceCall[e \in Elevator, c \in ElevatorCall] ==
    LET eState == ElevatorState[e] IN
    /\ c.floor = eState.floor
    /\ c.direction = eState.direction

PeopleWaiting[f \in Floor, d \in Direction] ==
    {p \in Person :
        /\ PersonState[p].location = f
        /\ PersonState[p].waiting
        /\ PersonState[p].location \in Floor
        /\ GetDirection[f, PersonState[p].destination] = d}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
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

SafetyInvariant ==
    \* A person riding an elevator, not yet at their destination, has that
    \* destination's button pressed in the elevator
    /\ \A p \in Person :
        PersonState[p].location \in Elevator =>
            LET e == PersonState[p].location IN
            (ElevatorState[e].floor /= PersonState[p].destination) =>
                PersonState[p].destination \in ElevatorState[e].buttonsPressed
    \* A person riding an elevator is always waiting (not yet arrived)
    /\ \A p \in Person :
        PersonState[p].location \in Elevator => PersonState[p].waiting
    \* No active call exists without somebody waiting for it
    /\ \A c \in ActiveElevatorCalls : PeopleWaiting[c.floor, c.direction] /= {}

TemporalInvariant ==
    \* Every active call is eventually serviced by some elevator
    /\ \A c \in ElevatorCall :
        (c \in ActiveElevatorCalls) ~> (\E e \in Elevator : CanServiceCall[e, c])
    \* Every waiting person eventually reaches their destination
    /\ \A p \in Person :
        PersonState[p].waiting ~>
            (/\ ~PersonState[p].waiting
             /\ PersonState[p].location = PersonState[p].destination)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A person on a floor, not waiting, picks a new destination floor
PickNewDestination(p) ==
    LET pState == PersonState[p] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ \E f \in Floor :
        /\ f /= pState.location
        /\ PersonState' = [PersonState EXCEPT ![p].destination = f]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

\* A person calls the elevator to go in the direction of their destination
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

\* Elevator doors open to service a call or let passengers out
OpenElevatorDoors(e) ==
    LET eState == ElevatorState[e] IN
    /\ ~eState.doorsOpen
    /\ \/ \E call \in ActiveElevatorCalls : CanServiceCall[e, call]
       \/ eState.floor \in eState.buttonsPressed
    /\ ElevatorState' = [ElevatorState EXCEPT
                            ![e].doorsOpen = TRUE,
                            ![e].buttonsPressed = @ \ {eState.floor}]
    /\ ActiveElevatorCalls' =
        ActiveElevatorCalls \ {[floor |-> eState.floor, direction |-> eState.direction]}
    /\ UNCHANGED <<PersonState>>

\* People waiting on the floor in the elevator's direction get on
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

\* People whose destination is the current floor get off
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

\* Doors close once nobody else is entering or exiting
CloseElevatorDoors(e) ==
    LET eState == ElevatorState[e] IN
    /\ ~ENABLED EnterElevator(e)
    /\ ~ENABLED ExitElevator(e)
    /\ eState.doorsOpen
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].doorsOpen = FALSE]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

\* Elevator moves one floor in its current direction
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
            \E e2 \in Elevator :
                /\ e /= e2
                /\ CanServiceCall[e2, call]
    /\ nextFloor \in Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].floor = nextFloor]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

\* Elevator stops at the end of its travel range
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

\* Dispatch the nearest eligible elevator (stationary, or already
\* approaching in the call's direction) to an active call. This is a simple
\* policy, not a globally optimal scheduling algorithm.
DispatchElevator(c) ==
    LET stationary == {e \in Elevator : ElevatorState[e].direction = "Stationary"}
        approaching == {e \in Elevator :
                          /\ ElevatorState[e].direction = c.direction
                          /\ \/ ElevatorState[e].floor = c.floor
                             \/ GetDirection[ElevatorState[e].floor, c.floor] = c.direction}
        eligible == stationary \cup approaching
    IN
    /\ c \in ActiveElevatorCalls
    /\ eligible /= {}
    /\ LET closest == CHOOSE e \in eligible :
                        \A e2 \in eligible :
                            GetDistance[ElevatorState[e].floor, c.floor]
                                <= GetDistance[ElevatorState[e2].floor, c.floor]
       IN /\ closest \in stationary
          /\ ElevatorState' = [ElevatorState EXCEPT
                                  ![closest].floor = c.floor,
                                  ![closest].direction = c.direction]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

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

Next ==
    \/ \E p \in Person : PickNewDestination(p)
    \/ \E p \in Person : CallElevator(p)
    \/ \E e \in Elevator : OpenElevatorDoors(e)
    \/ \E e \in Elevator : EnterElevator(e)
    \/ \E e \in Elevator : ExitElevator(e)
    \/ \E e \in Elevator : CloseElevatorDoors(e)
    \/ \E e \in Elevator : MoveElevator(e)
    \/ \E e \in Elevator : StopElevator(e)
    \/ \E c \in ElevatorCall : DispatchElevator(c)

TemporalAssumptions ==
    /\ \A p \in Person : WF_Vars(CallElevator(p))
    /\ \A e \in Elevator : WF_Vars(OpenElevatorDoors(e))
    /\ \A e \in Elevator : WF_Vars(EnterElevator(e))
    /\ \A e \in Elevator : WF_Vars(ExitElevator(e))
    /\ \A e \in Elevator : SF_Vars(CloseElevatorDoors(e))
    /\ \A e \in Elevator : SF_Vars(MoveElevator(e))
    /\ \A e \in Elevator : WF_Vars(StopElevator(e))
    /\ \A c \in ElevatorCall : SF_Vars(DispatchElevator(c))

Spec ==
    /\ Init
    /\ [][Next]_Vars
    /\ TemporalAssumptions

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant /\ TemporalInvariant)

=============================================================================