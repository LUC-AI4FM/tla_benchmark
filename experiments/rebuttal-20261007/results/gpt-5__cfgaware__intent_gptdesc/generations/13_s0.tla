---- MODULE RollingUpdate ----
EXTENDS TLC

CONSTANTS
  SERVERS,   \* Finite nonempty set of servers
  OLD,       \* A value denoting the old/running version
  UPDATING,  \* Distinguished intermediate non-serving state (parameter)
  NEW        \* A value denoting the new/running version

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
  vs,        \* Version state mapping: [SERVERS -> {OLD, UPDATING, NEW}]
  inLB,      \* Set of servers currently receiving traffic
  allowed    \* Set of servers permitted to start updating (when off LB)

vars == << vs, inLB, allowed >>

VersionStates == {OLD, UPDATING, NEW}
Runnable == {OLD, NEW}

TypeInv ==
  /\ vs \in [SERVERS -> VersionStates]
  /\ inLB \subseteq SERVERS
  /\ allowed \subseteq SERVERS

ServingNonEmpty == inLB # {}
ServingRunnable == \A s \in inLB: vs[s] \in Runnable
LBHomogeneous ==
  (inLB = {}) \/ (\E v \in Runnable: \A s \in inLB: vs[s] = v)

Safety == [] (ServingNonEmpty /\ ServingRunnable /\ LBHomogeneous)
ZeroDowntime == [] (ServingNonEmpty /\ ServingRunnable)
AllUpdated == \A s \in SERVERS: vs[s] = NEW
Termination == <> AllUpdated

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
  /\ vs \in [SERVERS -> VersionStates]
  /\ \A s \in SERVERS: vs[s] = OLD
  /\ inLB = SERVERS
  /\ allowed = {}

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Orchestrator removes one OLD server from LB and allows it to update.
RemoveAndAllow(s) ==
  /\ s \in SERVERS
  /\ s \in inLB
  /\ vs[s] = OLD
  /\ inLB \ {s} # {}              \* preserve zero-downtime
  /\ inLB' = inLB \ {s}
  /\ allowed' = allowed \cup {s}
  /\ vs' = vs

\* Orchestrator allows an off-LB OLD server to start updating.
AllowUpdateOffLB(s) ==
  /\ s \in SERVERS
  /\ s \notin inLB
  /\ vs[s] = OLD
  /\ s \notin allowed
  /\ allowed' = allowed \cup {s}
  /\ UNCHANGED << vs, inLB >>

\* Server starts its update when allowed and off LB.
StartUpdate(s) ==
  /\ s \in SERVERS
  /\ s \in allowed
  /\ s \notin inLB
  /\ vs[s] = OLD
  /\ vs' = [vs EXCEPT ![s] = UPDATING]
  /\ allowed' = allowed \ {s}
  /\ UNCHANGED inLB

\* Server completes its update, becoming NEW (always enabled while UPDATING).
FinishUpdate(s) ==
  /\ s \in SERVERS
  /\ vs[s] = UPDATING
  /\ vs' = [vs EXCEPT ![s] = NEW]
  /\ UNCHANGED << inLB, allowed >>

\* Orchestrator atomically switches traffic from all OLD in-LB servers
\* to a nonempty set of NEW servers that are off LB (ensures homogeneity and zero downtime).
SwitchTraffic ==
  /\ inLB # {}
  /\ \A s \in inLB: vs[s] = OLD
  /\ \E Add \in SUBSET (SERVERS \ inLB):
        /\ Add # {}
        /\ \A s \in Add: vs[s] = NEW
        /\ inLB' = Add
        /\ UNCHANGED << vs, allowed >>

\* Orchestrator returns a NEW server to the LB when the LB is already NEW-only.
ReturnNew(s) ==
  /\ s \in SERVERS
  /\ s \notin inLB
  /\ vs[s] = NEW
  /\ inLB # {}
  /\ \A t \in inLB: vs[t] = NEW
  /\ inLB' = inLB \cup {s}
  /\ UNCHANGED << vs, allowed >>

Next ==
  \E s \in SERVERS:
      RemoveAndAllow(s)
    \/ AllowUpdateOffLB(s)
    \/ StartUpdate(s)
    \/ FinishUpdate(s)
    \/ ReturnNew(s)
  \/ SwitchTraffic

(***************************************************************************)
(* Fairness: ensure progress/termination                                   *)
(* - Every off-LB update that is enabled will eventually be initiated and   *)
(*   completed.                                                             *)
(* - Traffic switch eventually occurs once continuously enabled.            *)
(***************************************************************************)
Fairness ==
  /\ \A s \in SERVERS: SF_vars(RemoveAndAllow(s))
  /\ \A s \in SERVERS: SF_vars(AllowUpdateOffLB(s))
  /\ \A s \in SERVERS: SF_vars(StartUpdate(s))
  /\ \A s \in SERVERS: WF_vars(FinishUpdate(s))
  /\ SF_vars(SwitchTraffic)

Spec ==
  Init /\ [][Next]_vars /\ Fairness

====