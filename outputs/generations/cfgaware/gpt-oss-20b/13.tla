\*======================================================================
\*  RollingDeployment.tla
\*
\*  This specification models a rolling deployment of software across a small
\*  set of servers behind a load balancer.  One process updates individual
\*  servers, while a separate coordinator removes servers from the load
\*  balancer, triggers updates, waits for completion, and then restores
\*  service, preserving availability during deployment.
\*
\*  The specification defines:
\*      • Constants: SERVERS
\*      • Variables: lbServers, serverStatus, removedServers, coordState
\*      • Operators: Init, UpdateStep, CoordStep, Next, Spec
\*
\*  The temporal specification is:
\*      Spec == Init /\ [][Next]_vars /\ WF_vars[UpdateStep] /\ WF_vars[CoordStep]
\*======================================================================
module RollingDeployment

EXTENDS Naturals

CONSTANTS SERVERS

VARIABLES lbServers, serverStatus, removedServers, coordState

(*--------------------------------------------------------------------
  Type invariant (optional but useful for model checking)
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ lbServers \subseteq SERVERS
  /\ removedServers \subseteq SERVERS
  /\ serverStatus ∈ [SERVERS -> {"idle","updating","updated"}]
  /\ coordState ∈ {"idle", "waiting"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ lbServers = SERVERS
  /\ removedServers = {}
  /\ serverStatus = [s ∈ SERVERS |-> "idle"]
  /\ coordState = "idle"

(*--------------------------------------------------------------------
  Coordinator actions
--------------------------------------------------------------------*)

IdleRemove ==
  /\ coordState = "idle"
  /\ \E s \in lbServers :
      /\ lbServers'   = lbServers \ {s}
      /\ removedServers' = removedServers ∪ {s}
      /\ serverStatus' = [serverStatus EXCEPT ![s] = "updating"]
      /\ coordState'   = "waiting"

WaitingRestore ==
  /\ coordState = "waiting"
  /\ \A s \in SERVERS : serverStatus[s] # "updating"          (* all updates finished *)
  /\ lbServers'   = lbServers ∪ removedServers
  /\ removedServers' = {}
  /\ coordState'   = "idle"

CoordStep == IdleRemove \/ WaitingRestore

(*--------------------------------------------------------------------
  Per‑server update action
--------------------------------------------------------------------*)
UpdateStep ==
  /\ \E s \in SERVERS :
      /\ serverStatus[s] = "updating"
      /\ serverStatus' = [serverStatus EXCEPT ![s] = "updated"]
      /\ UNCHANGED <<lbServers, removedServers, coordState>>

(*--------------------------------------------------------------------
  Next state relation
--------------------------------------------------------------------*)
Next == UpdateStep \/ CoordStep

vars == <<lbServers, serverStatus, removedServers, coordState>>

(*--------------------------------------------------------------------
  Temporal specification with weak fairness for both processes
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars[UpdateStep] /\ WF_vars[CoordStep]

=============================================================================
*======================================================================
* End of module RollingDeployment.tla
*======================================================================