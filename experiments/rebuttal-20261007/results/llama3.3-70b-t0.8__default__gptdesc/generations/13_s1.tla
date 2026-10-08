```
MODULE RollingDeployment
EXTENDS Integers, FiniteSets

CONSTANTS Servers, UpdateTime
VARIABLES serverStatus, loadBalancer, updatingServer, coordinatorState,
          updateComplete, currentServer

Init ==
  /\ serverStatus \in [Servers |-> "idle"]
  /\ loadBalancer = Servers
  /\ updatingServer = NULL
  /\ coordinatorState = "idle"
  /\ updateComplete = {}
  /\ currentServer = ChooseServer(Servers)

Next ==
  /\ (coordinatorState = "idle") => 
    /\ IF currentServer \in loadBalancer THEN
        /\ updatingServer = currentServer
        /\ coordinatorState = "updating"
      ELSE
        /\ currentServer = ChooseServer(Servers \ updateComplete)
        /\ updateComplete = updateComplete \cup {currentServer}
    /\ (coordinatorState = "updating") =>
      /\ IF serverStatus[updatingServer] = "done" THEN
          /\ loadBalancer = loadBalancer \cup {updatingServer}
          /\ coordinatorState = "idle"
          /\ updateComplete = updateComplete \cup {updatingServer}
        ELSE
          /\ serverStatus[updatingServer] = "updating"
  /\ (serverStatus[updatingServer] = "updating") =>
    /\ IF updatingServer \in loadBalancer THEN
        /\ loadBalancer = loadBalancer \ {updatingServer}
      /\ serverStatus[updatingServer] = "done" 

ChooseServer(s) == CHOOSE x \in s : TRUE

Spec == Init /\ [][Next]_<<serverStatus, loadBalancer, updatingServer, 
                                        coordinatorState, updateComplete, currentServer>>
Fairness == WF_vars(Next, <<serverStatus, loadBalancer, updatingServer, 
                                   coordinatorState, updateComplete, currentServer>>)

THEOREM Spec => []~<>(coordinatorState = "idle" /\ updateComplete = Servers)
```