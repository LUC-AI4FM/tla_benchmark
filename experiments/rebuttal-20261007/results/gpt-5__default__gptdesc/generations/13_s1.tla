----------------------------- MODULE RollingDeploy -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  SERVERS,
  MinInService

ASSUME
  /\ SERVERS # {}
  /\ IsFiniteSet(SERVERS)
  /\ MinInService \in Nat
  /\ MinInService >= 1
  /\ MinInService < Cardinality(SERVERS)

VARIABLES
  mode,    \* [SERVERS -> {"InLB","OutLB"}]
  sw,      \* [SERVERS -> {"Old","New"}]
  phase,   \* [SERVERS -> {"Idle","Updating"}]
  cstate,  \* {"Idle","Draining","WaitingUpdate"}
  ctarget

vars == <<mode, sw, phase, cstate, ctarget>>

LBStates == {"InLB", "OutLB"}
SWVersions == {"Old", "New"}
Phases == {"Idle", "Updating"}
CStates == {"Idle", "Draining", "WaitingUpdate"}

InLBSet == {s \in SERVERS: mode[s] = "InLB"}
UpdatingSet == {s \in SERVERS: phase[s] = "Updating"}

TypeOK ==
  /\ mode \in [SERVERS -> LBStates]
  /\ sw \in [SERVERS -> SWVersions]
  /\ phase \in [SERVERS -> Phases]
  /\ cstate \in CStates
  /\ ctarget \in SERVERS \cup {Nil}

Init ==
  /\ mode = [s \in SERVERS |-> "InLB"]
  /\ sw = [s \in SERVERS |-> "Old"]
  /\ phase = [s \in SERVERS |-> "Idle"]
  /\ cstate = "Idle"
  /\ ctarget = Nil

\* Coordinator removes a server from LB when doing so preserves availability.
CoordRemove ==
  /\ cstate = "Idle"
  /\ \E s \in SERVERS:
        /\ sw[s] = "Old"
        /\ mode[s] = "InLB"
        /\ Cardinality(InLBSet) > MinInService
        /\ mode' = [mode EXCEPT ![s] = "OutLB"]
        /\ ctarget' = s
        /\ cstate' = "Draining"
        /\ UNCHANGED <<sw, phase>>

\* Coordinator triggers the server update off LB.
CoordTriggerUpdate ==
  /\ cstate = "Draining"
  /\ ctarget \in SERVERS
  /\ sw[ctarget] = "Old"
  /\ mode[ctarget] = "OutLB"
  /\ phase[ctarget] = "Idle"
  /\ phase' = [phase EXCEPT ![ctarget] = "Updating"]
  /\ cstate' = "WaitingUpdate"
  /\ UNCHANGED <<mode, sw, ctarget>>

\* Server process completes the update when triggered.
ServerUpdate(s) ==
  /\ s \in SERVERS
  /\ phase[s] = "Updating"
  /\ mode[s] = "OutLB"
  /\ sw' = [sw EXCEPT ![s] = "New"]
  /\ phase' = [phase EXCEPT ![s] = "Idle"]
  /\ UNCHANGED <<mode, cstate, ctarget>>

ServerStep == \E s \in SERVERS: ServerUpdate(s)

\* Coordinator restores the server to LB after update completion.
CoordRestore ==
  /\ cstate = "WaitingUpdate"
  /\ ctarget \in SERVERS
  /\ sw[ctarget] = "New"
  /\ phase[ctarget] = "Idle"
  /\ mode[ctarget] = "OutLB"
  /\ mode' = [mode EXCEPT ![ctarget] = "InLB"]
  /\ cstate' = "Idle"
  /\ ctarget' = Nil
  /\ UNCHANGED <<sw, phase>>

CoordStep == CoordRemove \/ CoordTriggerUpdate \/ CoordRestore

Next == CoordStep \/ ServerStep

\* Safety invariants
AvailabilityInvariant == Cardinality(InLBSet) >= MinInService
UpdateOnlyOutOfLB == \A s \in SERVERS: phase[s] = "Updating" => mode[s] = "OutLB"
AtMostOneUpdating == Cardinality(UpdatingSet) <= 1
CoordinatorConsistency ==
  /\ (cstate = "Idle") => ctarget = Nil
  /\ (cstate # "Idle") => ctarget \in SERVERS

Safety == TypeOK /\ AvailabilityInvariant /\ UpdateOnlyOutOfLB /\ AtMostOneUpdating /\ CoordinatorConsistency

\* Liveness: eventual completion (all updated, restored, and coordinator idle)
AllUpdatedRestored ==
  /\ \A s \in SERVERS: sw[s] = "New" /\ phase[s] = "Idle" /\ mode[s] = "InLB"
  /\ cstate = "Idle"
  /\ ctarget = Nil

Termination == <>(AllUpdatedRestored)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordStep)
  /\ WF_vars(ServerStep)
=============================================================================