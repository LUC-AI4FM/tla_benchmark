--------------------------- MODULE RollingDeployment ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    SERVERS, \* finite, non-empty set of servers
    MinAvail \* minimum number of servers that must remain in the load balancer

ASSUME /\ SERVERS # {}
       /\ IsFiniteSet(SERVERS)
       /\ MinAvail \in Nat
       /\ MinAvail >= 1
       /\ Cardinality(SERVERS) >= MinAvail + 1

(*
 State
*)
VARIABLES
    lb,            \* subset of SERVERS currently in the load balancer
    version,       \* [SERVERS -> {"Old","New"}]
    updating,      \* [SERVERS -> BOOLEAN], per-server update in progress
    req,           \* requested server to update (from coordinator to updater) or Null
    ack,           \* acknowledgement of completed update (from updater to coordinator) or Null
    coordPhase,    \* {"idle","wait","done"}
    target,        \* current server being rolled by coordinator or Null
    updaterPhase   \* {"idle","updating"}

Null == CHOOSE x : x \notin SERVERS

CoordPhases == {"idle","wait","done"}
UpdaterPhases == {"idle","updating"}

vars == << lb, version, updating, req, ack, coordPhase, target, updaterPhase >>

TypeOK ==
    /\ lb \subseteq SERVERS
    /\ version \in [SERVERS -> {"Old","New"}]
    /\ updating \in [SERVERS -> BOOLEAN]
    /\ req \in SERVERS \cup {Null}
    /\ ack \in SERVERS \cup {Null}
    /\ coordPhase \in CoordPhases
    /\ target \in SERVERS \cup {Null}
    /\ updaterPhase \in UpdaterPhases

AllUpdated == \A s \in SERVERS : version[s] = "New"

OldInLB == { s \in lb : version[s] = "Old" }

Init ==
    /\ lb = SERVERS
    /\ version = [s \in SERVERS |-> "Old"]
    /\ updating = [s \in SERVERS |-> FALSE]
    /\ req = Null
    /\ ack = Null
    /\ coordPhase = "idle"
    /\ target = Null
    /\ updaterPhase = "idle"
    /\ TypeOK

(*
 Coordinator actions
*)
CoordinatorStart ==
    /\ coordPhase = "idle"
    /\ updaterPhase = "idle"
    /\ req = Null
    /\ ack = Null
    /\ target = Null
    /\ OldInLB # {}
    /\ Cardinality(lb) > MinAvail
    /\ \E s \in OldInLB :
         /\ lb' = lb \ {s}
         /\ target' = s
         /\ req' = s
         /\ coordPhase' = "wait"
         /\ UNCHANGED << version, updating, ack, updaterPhase >>
    /\ TypeOK'

CoordinatorRestore ==
    /\ coordPhase = "wait"
    /\ target \in SERVERS
    /\ req = Null
    /\ ack = target
    /\ updaterPhase = "idle"
    /\ updating[target] = FALSE
    /\ version[target] = "New"
    /\ lb' = lb \cup {target}
    /\ ack' = Null
    /\ target' = Null
    /\ coordPhase' = IF AllUpdated THEN "done" ELSE "idle"
    /\ UNCHANGED << version, updating, req, updaterPhase >>
    /\ TypeOK'

CoordinatorFinishNoWork ==
    /\ coordPhase = "idle"
    /\ updaterPhase = "idle"
    /\ req = Null
    /\ ack = Null
    /\ target = Null
    /\ AllUpdated
    /\ coordPhase' = "done"
    /\ UNCHANGED << lb, version, updating, req, ack, target, updaterPhase >>
    /\ TypeOK'

CoordinatorStep == CoordinatorStart \/ CoordinatorRestore \/ CoordinatorFinishNoWork

(*
 Updater actions
*)
UpdaterBegin ==
    /\ updaterPhase = "idle"
    /\ req \in SERVERS
    /\ target = req
    /\ updating[req] = FALSE
    /\ updaterPhase' = "updating"
    /\ updating' = [updating EXCEPT ![req] = TRUE]
    /\ UNCHANGED << lb, version, req, ack, coordPhase, target >>
    /\ TypeOK'

UpdaterFinish ==
    /\ updaterPhase = "updating"
    /\ \E s \in SERVERS : updating[s] = TRUE
    /\ \E s \in SERVERS :
         /\ updating[s] = TRUE
         /\ version' = [version EXCEPT ![s] = "New"]
         /\ updating' = [updating EXCEPT ![s] = FALSE]
         /\ updaterPhase' = "idle"
         /\ req' = Null
         /\ ack' = s
         /\ UNCHANGED << lb, coordPhase, target >>
    /\ TypeOK'

UpdaterStep == UpdaterBegin \/ UpdaterFinish

Next == CoordinatorStep \/ UpdaterStep

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorStep) /\ WF_vars(UpdaterStep)

(*
 Safety invariants
*)
InvAvail ==
    Cardinality(lb) >= MinAvail

InvNoServiceDuringUpdate ==
    \A s \in lb : ~updating[s]

InvSingleUpdating ==
    LET U == { s \in SERVERS : updating[s] } IN Cardinality(U) \in {0, 1}

SafetyInv == TypeOK /\ InvAvail /\ InvNoServiceDuringUpdate /\ InvSingleUpdating

(*
 Termination (eventual completion of all processes)
*)
Terminated ==
    /\ coordPhase = "done"
    /\ updaterPhase = "idle"
    /\ AllUpdated
    /\ req = Null
    /\ ack = Null
    /\ target = Null
    /\ lb = SERVERS

Termination == <> Terminated
=============================================================================