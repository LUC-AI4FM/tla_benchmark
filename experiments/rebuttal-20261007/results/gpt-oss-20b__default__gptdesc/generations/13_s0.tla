MODULE RollingDeployment
EXTENDS Naturals, TLC

CONSTANTS SERVERS, None

VARIABLES status, lbServers, coordinatorState, curS

Init ==
  /\ status = [s ∈ SERVERS |-> "running"]
  /\ lbServers = SERVERS
  /\ coordinatorState = "idle"
  /\ curS = None

PerServerUpdate(s) ==
  /\ s ∈ SERVERS
  /\ status[s] = "updating"
  /\ status' = [status EXCEPT ![s] = "running"]
  /\ UNCHANGED <<lbServers, coordinatorState, curS>>

RemoveServer(s) ==
  /\ coordinatorState = "idle"
  /\ s ∈ lbServers
  /\ lbServers' = lbServers \ {s}
  /\ curS' = s
  /\ coordinatorState' = "removing"
  /\ UNCHANGED status

TriggerUpdate ==
  /\ coordinatorState = "removing"
  /\ status[curS] = "running"
  /\ status' = [status EXCEPT ![curS] = "updating"]
  /\ coordinatorState' = "waiting"
  /\ UNCHANGED <<lbServers, curS>>

WaitDone ==
  /\ coordinatorState = "waiting"
  /\ status[curS] = "running"
  /\ coordinatorState' = "restoring"
  /\ UNCHANGED <<status, lbServers, curS>>

RestoreServer ==
  /\ coordinatorState = "restoring"
  /\ lbServers' = lbServers ∪ {curS}
  /\ curS' = None
  /\ coordinatorState' = "idle"
  /\ UNCHANGED status

UpdateAll == \vee_{s ∈ SERVERS} PerServerUpdate(s)

CoordinatorAction ==
  (\vee_{s ∈ SERVERS} RemoveServer(s))
  \/ TriggerUpdate
  \/ WaitDone
  \/ RestoreServer

Next == UpdateAll \/ CoordinatorAction

Avail == Cardinality(lbServers) >= 1

Termination ==
  /\ \A s ∈ SERVERS : status[s] = "running"
  /\ lbServers = SERVERS
  /\ coordinatorState = "idle"

Spec == Init
        /\ [][Next]_vars
        /\ WF_vars[UpdateAll]
        /\ WF_vars[CoordinatorAction]
        /\ []Avail
        /\ <>Termination

END MODULE