------------------------------ MODULE RollingDeployment ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Servers, MinAvail, None

ASSUME /\ IsFiniteSet(Servers)
       /\ Servers # {}
       /\ None \notin Servers
       /\ MinAvail \in Nat
       /\ 1 \leq MinAvail
       /\ MinAvail < Cardinality(Servers)

VARIABLES inLB, status, coordPhase, coordTarget, updateReq, updPhase, updTarget

vars == << inLB, status, coordPhase, coordTarget, updateReq, updPhase, updTarget >>

StatusVals == {"old", "updating", "new"}
CoordPhases == {"idle", "remove", "trigger", "wait", "done"}
UpdPhases == {"idle", "updating"}

AllUpdated == \A s \in Servers: status[s] = "new"

TypeOK ==
  /\ inLB \subseteq Servers
  /\ status \in [Servers -> StatusVals]
  /\ coordPhase \in CoordPhases
  /\ coordTarget \in (Servers \cup {None})
  /\ updateReq \in (Servers \cup {None})
  /\ updPhase \in UpdPhases
  /\ updTarget \in (Servers \cup {None})

UpdatingSet == { s \in Servers: status[s] = "updating" }

AvailabilityInv == Cardinality(inLB) \geq MinAvail

SingleOutInv == Cardinality(Servers \ inLB) \leq 1

RollingInv ==
  \A s \in Servers: status[s] = "updating" => s \notin inLB

RemovedIsTargetInv ==
  (Servers \ inLB) \subseteq IF coordTarget \in Servers THEN {coordTarget} ELSE {}

AtMostOneUpdating == Cardinality(UpdatingSet) \leq 1

Inv == TypeOK /\ AvailabilityInv /\ SingleOutInv /\ RollingInv /\ RemovedIsTargetInv /\ AtMostOneUpdating

Init ==
  /\ inLB = Servers
  /\ status = [s \in Servers |-> "old"]
  /\ coordPhase = "idle"
  /\ coordTarget = None
  /\ updateReq = None
  /\ updPhase = "idle"
  /\ updTarget = None

CoordChoose(t) ==
  /\ coordPhase = "idle"
  /\ ~AllUpdated
  /\ t \in Servers
  /\ status[t] = "old"
  /\ coordPhase' = "remove"
  /\ coordTarget' = t
  /\ UNCHANGED << inLB, status, updateReq, updPhase, updTarget >>

CoordRemove ==
  /\ coordPhase = "remove"
  /\ coordTarget \in Servers
  /\ coordTarget \in inLB
  /\ Cardinality(inLB) > MinAvail
  /\ inLB' = inLB \ {coordTarget}
  /\ coordPhase' = "trigger"
  /\ UNCHANGED << status, coordTarget, updateReq, updPhase, updTarget >>

CoordTrigger ==
  /\ coordPhase = "trigger"
  /\ updateReq = None
  /\ updateReq' = coordTarget
  /\ coordPhase' = "wait"
  /\ UNCHANGED << inLB, status, coordTarget, updPhase, updTarget >>

CoordRestore ==
  /\ coordPhase = "wait"
  /\ coordTarget \in Servers
  /\ status[coordTarget] = "new"
  /\ coordTarget \notin inLB
  /\ inLB' = inLB \cup {coordTarget}
  /\ coordTarget' = None
  /\ coordPhase' = IF AllUpdated THEN "done" ELSE "idle"
  /\ UNCHANGED << status, updateReq, updPhase, updTarget >>

CoordFinish ==
  /\ coordPhase = "idle"
  /\ AllUpdated
  /\ coordPhase' = "done"
  /\ UNCHANGED << inLB, status, coordTarget, updateReq, updPhase, updTarget >>

UpdAccept ==
  /\ updPhase = "idle"
  /\ updateReq \in Servers
  /\ status[updateReq] = "old"
  /\ updateReq \notin inLB
  /\ updTarget' = updateReq
  /\ updPhase' = "updating"
  /\ status' = [status EXCEPT ![updateReq] = "updating"]
  /\ updateReq' = None
  /\ UNCHANGED << inLB, coordPhase, coordTarget >>

UpdComplete ==
  /\ updPhase = "updating"
  /\ updTarget \in Servers
  /\ status[updTarget] = "updating"
  /\ updPhase' = "idle"
  /\ status' = [status EXCEPT ![updTarget] = "new"]
  /\ updTarget' = None
  /\ UNCHANGED << inLB, coordPhase, coordTarget, updateReq >>

CoordinatorAction ==
  (\E t \in Servers: CoordChoose(t)) \/ CoordRemove \/ CoordTrigger \/ CoordRestore \/ CoordFinish

UpdaterAction == UpdAccept \/ UpdComplete

Next ==
  (\E t \in Servers: CoordChoose(t))
  \/ CoordRemove
  \/ CoordTrigger
  \/ CoordRestore
  \/ CoordFinish
  \/ UpdAccept
  \/ UpdComplete

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorAction) /\ WF_vars(UpdaterAction)

Termination == <> (AllUpdated /\ coordPhase = "done" /\ updPhase = "idle")

======================================================================================