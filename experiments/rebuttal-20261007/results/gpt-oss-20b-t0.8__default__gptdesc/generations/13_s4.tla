MODULE RollingDeployment

EXTENDS Naturals, Sequences, SETS

CONSTANTS SERVERS, Null

VARIABLES srvState, lbServers, coordPhase, curSrv

(* Type assumptions *)
TypeInvariant ==
  /\ srvState ∈ [SERVERS -> {"available","removed","updating","updated"}]
  /\ lbServers ⊆ SERVERS
  /\ coordPhase ∈ {"idle", "waiting", "restoring"}
  /\ curSrv ∈ SERVERS ∪ {Null}

(* Initial state *)
Init ==
  /\ srvState = [s \in SERVERS |-> "available"]
  /\ lbServers = SERVERS
  /\ coordPhase = "idle"
  /\ curSrv = Null

(* Actions *)

RemoveServer(s) ==
  /\ coordPhase = "idle"
  /\ s ∈ SERVERS
  /\ s ∈ lbServers
  /\ srvState[s] = "available"
  /\ LET newSrvState == [srvState EXCEPT ![s] = "removed"]
     IN
        /\ srvState' = newSrvState
        /\ lbServers' = lbServers \ {s}
        /\ curSrv' = s
        /\ coordPhase' = "waiting"

UpdateBegin(s) ==
  /\ srvState[s] = "removed"
  /\ srvState' = [srvState EXCEPT ![s] = "updating"]
  /\ UNCHANGED <<lbServers, coordPhase, curSrv>>

UpdateFinish(s) ==
  /\ srvState[s] = "updating"
  /\ srvState' = [srvState EXCEPT ![s] = "updated"]
  /\ UNCHANGED <<lbServers, coordPhase, curSrv>>

CheckUpdateComplete ==
  /\ coordPhase = "waiting"
  /\ curSrv ∈ SERVERS
  /\ srvState[curSrv] = "updated"
  /\ coordPhase' = "restoring"
  /\ UNCHANGED <<srvState, lbServers, curSrv>>

RestoreServer ==
  /\ coordPhase = "restoring"
  /\ curSrv ∈ SERVERS
  /\ srvState[curSrv] = "updated"
  /\ lbServers' = lbServers ∪ {curSrv}
  /\ coordPhase' = "idle"
  /\ curSrv' = Null
  /\ UNCHANGED <<srvState>>

Next ==
  \/∃ s ∈ SERVERS : RemoveServer(s)
  \/∃ s ∈ SERVERS : UpdateBegin(s)
  \/∃ s ∈ SERVERS : UpdateFinish(s)
  \/ CheckUpdateComplete
  \/ RestoreServer

(* Fairness actions *)
UpdateAction == ∃ s ∈ SERVERS : UpdateBegin(s) \/ UpdateFinish(s)
CoordAction   == RemoveServer(Null) \/ CheckUpdateComplete \/ RestoreServer

(* Safety invariants *)
Invariant1 ==
  ∀ s ∈ SERVERS : (s ∈ lbServers ⇔ srvState[s] = "available")

Invariant2 ==
  (curSrv = Null) ⇔ (coordPhase = "idle")

(* Termination property *)
Termination == ◇((∀ s ∈ SERVERS : srvState[s] = "updated") /\ (coordPhase = "idle"))

Spec ==
  Init
  /\ [][Next]_<<srvState, lbServers, coordPhase, curSrv>>
  /\ WF_vars(UpdateAction)
  /\ WF_vars(CoordAction)
  /\ Invariant1
  /\ Invariant2

===============================================================================