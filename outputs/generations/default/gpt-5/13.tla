------------------------ MODULE RollingDeployment ------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Servers, \* finite set of servers
  NONE     \* special value not in Servers, used as "no server"

ASSUME
  /\ Servers # {}
  /\ Cardinality(Servers) >= 2
  /\ NONE \notin Servers

VARIABLES
  LB,         \* set of servers currently in the load balancer
  srvVer,     \* function Servers -> {0,1}, 0=old version, 1=new version
  remaining,  \* set of servers yet to be updated by the coordinator
  current,    \* current server chosen by the coordinator, or NONE
  cPhase,     \* coordinator phase
  requested,  \* set of servers requested for update (at most one)
  busy,       \* updater busy flag
  utarget     \* server currently being updated by updater, or NONE

vars == << LB, srvVer, remaining, current, cPhase, requested, busy, utarget >>

Init ==
  /\ LB = Servers
  /\ srvVer = [s \in Servers |-> 0]
  /\ remaining = Servers
  /\ current = NONE
  /\ cPhase = "Pick"
  /\ requested = {}
  /\ busy = FALSE
  /\ utarget = NONE

\*---------------- Coordinator actions ----------------

CoordinatorPick ==
  /\ cPhase = "Pick"
  /\ current = NONE
  /\ remaining # {}
  /\ \E s \in remaining : Cardinality(LB \ {s}) >= 1
  /\ LET s == CHOOSE t \in remaining : Cardinality(LB \ {t}) >= 1 IN
       /\ current' = s
       /\ cPhase' = "Drain"
       /\ UNCHANGED << LB, srvVer, remaining, requested, busy, utarget >>

CoordinatorDrain ==
  /\ cPhase = "Drain"
  /\ current \in Servers
  /\ current \in LB
  /\ Cardinality(LB) >= 2
  /\ LB' = LB \ {current}
  /\ cPhase' = "Trigger"
  /\ UNCHANGED << srvVer, remaining, current, requested, busy, utarget >>

CoordinatorTrigger ==
  /\ cPhase = "Trigger"
  /\ current \in Servers
  /\ requested = {}
  /\ ~busy
  /\ requested' = {current}
  /\ cPhase' = "Wait"
  /\ UNCHANGED << LB, srvVer, remaining, current, busy, utarget >>

CoordinatorWait ==
  /\ cPhase = "Wait"
  /\ current \in Servers
  /\ requested = {}
  /\ ~busy
  /\ srvVer[current] = 1
  /\ cPhase' = "Restore"
  /\ UNCHANGED << LB, srvVer, remaining, current, requested, busy, utarget >>

CoordinatorRestore ==
  /\ cPhase = "Restore"
  /\ current \in Servers
  /\ LB' = LB \cup {current}
  /\ cPhase' = "Finish"
  /\ UNCHANGED << srvVer, remaining, current, requested, busy, utarget >>

CoordinatorFinish ==
  /\ cPhase = "Finish"
  /\ current \in Servers
  /\ remaining' = remaining \ {current}
  /\ current' = NONE
  /\ cPhase' = IF remaining' = {} THEN "Done" ELSE "Pick"
  /\ UNCHANGED << LB, srvVer, requested, busy, utarget >>

CoordinatorAct ==
  CoordinatorPick \/ CoordinatorDrain \/ CoordinatorTrigger \/
  CoordinatorWait \/ CoordinatorRestore \/ CoordinatorFinish

\*---------------- Updater actions ----------------

UpdaterStart ==
  /\ ~busy
  /\ utarget = NONE
  /\ requested # {}
  /\ LET s == CHOOSE t \in requested : TRUE IN
       /\ utarget' = s
       /\ busy' = TRUE
       /\ UNCHANGED << LB, srvVer, remaining, current, cPhase, requested >>

UpdaterFinish ==
  /\ busy
  /\ utarget \in requested
  /\ requested' = requested \ {utarget}
  /\ srvVer' = [srvVer EXCEPT ![utarget] = 1]
  /\ busy' = FALSE
  /\ utarget' = NONE
  /\ UNCHANGED << LB, remaining, current, cPhase >>

UpdaterAct ==
  UpdaterStart \/ UpdaterFinish

\*---------------- System step and specification ----------------

Next == CoordinatorAct \/ UpdaterAct

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordinatorAct)
  /\ WF_vars(UpdaterAct)

\*---------------- Safety invariants ----------------

TypeInv ==
  /\ LB \subseteq Servers
  /\ remaining \subseteq Servers
  /\ current \in (Servers \cup {NONE})
  /\ requested \subseteq Servers
  /\ utarget \in (Servers \cup {NONE})
  /\ srvVer \in [Servers -> {0,1}]
  /\ cPhase \in {"Pick","Drain","Trigger","Wait","Restore","Finish","Done"}
  /\ busy \in BOOLEAN

AvailabilityInv ==
  LB # {}

SingleRequestInv ==
  requested = {} \/ requested = {current}

BusyTargetInv ==
  busy => utarget \in requested

CurrentWhenActiveInv ==
  (cPhase \in {"Drain","Trigger","Wait","Restore","Finish"}) => current \in Servers

SafetyInv ==
  TypeInv /\ AvailabilityInv /\ SingleRequestInv /\ BusyTargetInv /\ CurrentWhenActiveInv

\*---------------- Liveness (termination) ----------------

Terminated ==
  /\ cPhase = "Done"
  /\ remaining = {}
  /\ current = NONE
  /\ ~busy
  /\ requested = {}
  /\ \A s \in Servers : srvVer[s] = 1

Termination ==
  <> Terminated

============================================================================