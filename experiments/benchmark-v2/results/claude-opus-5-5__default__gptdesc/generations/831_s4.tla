------------------------------ MODULE Elevator ------------------------------
EXTENDS Integers

CONSTANTS   Person,     \* The set of all people using the elevator system
            Elevator,   \* The set of all elevators
            FloorCount  \* The number of floors serviced by the elevator system

ASSUME FloorCount \in Nat \ {0}

VARIABLES   PersonState,            \* The state of each person
            ActiveElevatorCalls,    \* The set of all active elevator calls
            ElevatorState           \* The state of each elevator

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
    /\ c.floor = ElevatorState[e].floor
    /\ c.direction = ElevatorState[e].direction

PeopleWaiting[f \in Floor, d \in Direction] ==
    {p \in Person :
        /\ PersonState[p].location = f
        /\ PersonState[p].waiting
        /\ GetDirection[PersonState[p].location, PersonState[p].destination] = d}

-----------------------------------------------------------------------------
(* Invariants and properties *)

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
    \* A floor button is pressed only if a person in the elevator is going there
    /\ \A e \in Elevator :
        \A f \in ElevatorState[e].buttonsPressed :
            \E p \in Person :
                /\ PersonState[p].location = e
                /\ PersonState[p].destination = f
    \* A person is in an elevator only if it moves toward their destination
    /\ \A p \in Person :
        \A e \in Elevator :
            (/\ PersonState[p].location = e
             /\ ElevatorState[e].floor /= PersonState[p].destination)
                => ElevatorState[e].direction =
                     GetDirection[ElevatorState[e].floor, PersonState[p].destination]
    \* No ghost calls
    /\ \A c \in ActiveElevatorCalls : PeopleWaiting[c.floor, c.direction] /= {}

TemporalInvariant ==
    \* Every call is eventually serviced by an elevator
    /\ \A c \in ElevatorCall :
        (c \in ActiveElevatorCalls) ~> (\E e \in Elevator : CanServiceCall[e, c])
    \* Waiting people eventually reach their destination
    /\ \A p \in Person :
        PersonState[p].waiting ~> (PersonState[p].location = PersonState[p].destination)

-----------------------------------------------------------------------------
(* Actions *)

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
    LET call == [floor |-> pState.location,
                 direction |-> GetDirection[pState.location, pState.destination]] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ pState.location /= pState.destination
    /\ ActiveElevatorCalls' =
        IF \E e \in Elevator :
            /\ CanServiceCall[e, call]
            /\ ElevatorState[e].doorsOpen
        THEN ActiveElevatorCalls
        ELSE ActiveElevatorCalls \cup {call}
    /\ PersonState' = [PersonState EXCEPT ![p].waiting = TRUE]
    /\ UNCHANGED <<ElevatorState>>

OpenElevatorDoors(e) ==
    LET eState == ElevatorState[e] IN
    /\ ~eState.doorsOpen
    /\ \/ \E call \in ActiveElevatorCalls : CanServiceCall[e, call]
       \/ eState.floor \in eState.buttonsPressed
    /\ ElevatorState' = [ElevatorState EXCEPT
            ![e].doorsOpen = TRUE,
            ![e].buttonsPressed = eState.buttonsPressed \ {eState.floor}]
    /\ ActiveElevatorCalls' =
            ActiveElevatorCalls \ {[floor |-> eState.floor, direction |-> eState.direction]}
    /\ UNCHANGED <<PersonState>>

EnterElevator(e) ==
    LET eState == ElevatorState[e] IN
    /\ eState.doorsOpen
    /\ eState.direction /= "Stationary"
    /\ LET gettingOn == PeopleWaiting[eState.floor, eState.direction]
           destinations == {PersonState[p].destination : p \in gettingOn}
       IN
        /\ gettingOn /= {}
        /\ PersonState' = [p \in Person |->
                IF p \in gettingOn
                THEN [PersonState[p] EXCEPT !.location = e]
                ELSE PersonState[p]]
        /\ ElevatorState' = [ElevatorState EXCEPT
                ![e].buttonsPressed = eState.buttonsPressed \cup destinations]
    /\ UNCHANGED <<ActiveElevatorCalls>>

ExitElevator(e) ==
    LET eState == ElevatorState[e] IN
    LET gettingOff == {p \in Person :
                        /\ PersonState[p].location = e
                        /\ PersonState[p].destination = eState.floor} IN
    /\ eState.doorsOpen
    /\ gettingOff /= {}
    /\ PersonState' = [p \in Person |->
            IF p \in gettingOff
            THEN [PersonState[p] EXCEPT !.location = eState.floor, !.waiting = FALSE]
            ELSE PersonState[p]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CloseElevatorDoors(e) ==
    /\ ~ENABLED EnterElevator(e)
    /\ ~ENABLED ExitElevator(e)
    /\ ElevatorState[e].doorsOpen
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].doorsOpen = FALSE]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

MoveElevator(e) ==
    LET eState == ElevatorState[e] IN
    LET nextFloor == IF eState.direction = "Up"
                     THEN eState.floor + 1
                     ELSE eState.floor - 1 IN
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

StopElevator(e) ==
    LET eState == ElevatorState[e] IN
    LET nextFloor == IF eState.direction = "Up"
                     THEN eState.floor + 1
                     ELSE eState.floor - 1 IN
    /\ eState.direction /= "Stationary"
    /\ ~eState.doorsOpen
    /\ nextFloor \notin Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e].direction = "Stationary"]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

(***************************************************************************)
(* Dispatch: choose the closest elevator that is either stationary or     *)
(* already moving toward the call floor in the call's direction. This is  *)
(* a simple policy, not a globally optimal scheduling algorithm.          *)
(***************************************************************************)
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
       IN
        ElevatorState' =
            IF closest \in stationary
            THEN [ElevatorState EXCEPT ![closest].direction =
                    IF ElevatorState[closest].floor = c.floor
                    THEN c.direction
                    ELSE GetDirection[ElevatorState[closest].floor, c.floor]]
            ELSE ElevatorState
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

-----------------------------------------------------------------------------

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