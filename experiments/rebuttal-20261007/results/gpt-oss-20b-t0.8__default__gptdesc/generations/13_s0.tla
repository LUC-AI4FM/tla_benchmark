----------------------------- MODULE RollingDeployment -----------------------------
EXTENDS Naturals

CONSTANTS
    SERVERS \in SUBSET Nat,
    NULL

VARIABLES srvStatus, lb, coord, target

(* Type invariant for the variables *)
TypeInvariant ==
    /\ srvStatus \in [SERVERS -> {"outdated","updating","updated"}]
    /\ lb          \in SUBSET SERVERS
    /\ coord       \in {"idle", "removing", "updating", "restoring"}
    /\ target      \in SERVERS \/ {NULL}

Init ==
    /\ TypeInvariant
    /\ srvStatus = [s \in SERVERS |-> "outdated"]
    /\ lb        = SERVERS
    /\ coord     = "idle"
    /\ target    = NULL

COORD_REMOVE ==
    /\ coord = "idle"
    /\ (\E s \in lb : srvStatus[s] = "outdated")
    /\ target' \in {s \in lb : srvStatus[s]="outdated"}
    /\ target' \neq NULL
    /\ lb'     = lb \ {target'}
    /\ coord'  = "removing"
    /\ UNCHANGED <<srvStatus>>

COORD_TRIGGER ==
    /\ coord   = "removing"
    /\ target  /= NULL
    /\ srvStatus[target] = "outdated"
    /\ srvStatus'        = [srvStatus EXCEPT ![target] = "updating"]
    /\ coord'            = "updating"
    /\ UNCHANGED <<lb>>

SERVER_UPDATE ==
    /\ coord   = "updating"
    /\ target  /= NULL
    /\ srvStatus[target] = "updating"
    /\ srvStatus'        = [srvStatus EXCEPT ![target] = "updated"]
    /\ UNCHANGED <<lb, coord, target>>

COORD_WAIT ==
    /\ coord   = "updating"
    /\ target  /= NULL
    /\ srvStatus[target] = "updated"
    /\ coord'            = "restoring"
    /\ UNCHANGED <<srvStatus, lb, target>>

COORD_RESTORE ==
    /\ coord   = "restoring"
    /\ target  /= NULL
    /\ lb'     = lb \cup {target}
    /\ coord'  = "idle"
    /\ target' = NULL
    /\ UNCHANGED srvStatus

Next == COORD_REMOVE \/ COORD_TRIGGER \/ SERVER_UPDATE \/ COORD_WAIT \/ COORD_RESTORE

vars == <<srvStatus, lb, coord, target>>

(* Safety invariants *)
NOUPD_IN_LB ==
    \A s \in SERVERS : ~(srvStatus[s] = "updating" /\ s \in lb)

ATLEASTONE ==
    |\|lb| >= 1

SafetyInvariant == NOUPD_IN_LB /\ ATLEASTONE

(* Liveness property: eventual completion *)
Termination ==
    <> (coord = "idle" /\ (\A s \in SERVERS : srvStatus[s] = "updated"))

COORD_ACTION == COORD_REMOVE \/ COORD_TRIGGER \/ COORD_WAIT \/ COORD_RESTORE

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_enabled <<COORD_ACTION>>
    /\ WF_enabled <<SERVER_UPDATE>>
    /\ SafetyInvariant

=============================================================================