MODULE RollingDeployment
EXTENDS Naturals, FiniteSets

CONSTANT SERVERS

VARIABLES status, online

StatusSet == {"up-to-date", "outdated"}

Init ==
    /\ online = SERVERS
    /\ status \in [SERVERS -> StatusSet]
    /\ status = [s \in SERVERS |-> "up-to-date"]

Updater(s) ==
    /\ s \in SERVERS
    /\ status[s] = "outdated"
    /\ s \notin online
    /\ status' = [status EXCEPT ![s] = "up-to-date"]
    /\ online' = online

CoordRemove(s) ==
    /\ s \in SERVERS
    /\ s \in online
    /\ status[s] = "outdated"
    /\ online' = online \ {s}
    /\ status' = status

CoordAdd(s) ==
    /\ s \in SERVERS
    /\ s \notin online
    /\ status[s] = "up-to-date"
    /\ online' = online ∪ {s}
    /\ status' = status

Next == 
    \/ \E s \in SERVERS : Updater(s)
    \/ \E s \in SERVERS : CoordRemove(s)
    \/ \E s \in SERVERS : CoordAdd(s)

vars == {status, online}

OnlineStatusInv ==
    \A s \in online : status[s] = "up-to-date"

AvailabilityInv ==
    IF (\E s \in SERVERS : status[s] = "outdated") THEN
        1 <= |online|
    ELSE TRUE

Inv == OnlineStatusInv /\ AvailabilityInv

UpdaterAction == \E s \in SERVERS : Updater(s)
CoordinatorAction == \E s \in SERVERS : (CoordRemove(s) \/ CoordAdd(s))

Spec == Init /\ [][Next]_vars /\ WF(UpdaterAction) /\ WF(CoordinatorAction) /\ []Inv
===============================================================================