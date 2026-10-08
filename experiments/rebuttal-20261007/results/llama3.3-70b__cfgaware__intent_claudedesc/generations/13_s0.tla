--------------------------- MODULE RollingDeployment ---------------------------
EXTENDS Integers, TLC

CONSTANT Servers, InitialVersion, NewVersion
VARIABLES loadBalancer, serverStatus, updatePhase

Spec == 
  /\ loadBalancer \in [Servers -> {InitialVersion, NewVersion}]
  /\ serverStatus \in [Servers -> { idle, updating, updated }]
  /\ updatePhase \in { phase1, phase2, done }
  /\ Init
  /\ [][Next]_loadBalancer
  /\ WF_vars(Next)_(loadBalancer, serverStatus, updatePhase)

Init ==
  /\ loadBalancer = [s \in Servers |-> InitialVersion]
  /\ serverStatus = [s \in Servers |-> idle]
  /\ updatePhase = phase1

TypeInvariant ==
  /\ loadBalancer \in [Servers -> {InitialVersion, NewVersion}]
  /\ serverStatus \in [Servers -> { idle, updating, updated }]
  /\ updatePhase \in { phase1, phase2, done }

Next ==
  \/ \E s \in Servers :
      /\ updatePhase = phase1
      /\ serverStatus[s] = idle
      /\ loadBalancer' = [loadBalancer EXCEPT ![s] = NewVersion]
      /\ serverStatus' = [serverStatus EXCEPT ![s] = updating]
      /\ updatePhase' = phase1
  \/ \E s \in Servers :
      /\ updatePhase = phase1
      /\ serverStatus[s] = updating
      /\ serverStatus' = [serverStatus EXCEPT ![s] = updated]
      /\ loadBalancer' = loadBalancer
      /\ updatePhase' = IF \A t \in Servers : serverStatus[t] /= idle THEN phase2 ELSE phase1
  \/ \E s \in Servers :
      /\ updatePhase = phase2
      /\ serverStatus[s] = idle
      /\ loadBalancer' = [loadBalancer EXCEPT ![s] = NewVersion]
      /\ serverStatus' = [serverStatus EXCEPT ![s] = updating]
      /\ updatePhase' = phase2
  \/ \E s \in Servers :
      /\ updatePhase = phase2
      /\ serverStatus[s] = updating
      /\ serverStatus' = [serverStatus EXCEPT ![s] = updated]
      /\ loadBalancer' = loadBalancer
      /\ updatePhase' = IF \A t \in Servers : serverStatus[t] /= idle THEN done ELSE phase2
  \/ updatePhase = done
    /\ loadBalancer' = loadBalancer
    /\ serverStatus' = serverStatus
    /\ updatePhase' = done

ZeroDowntime == 
  \A s \in Servers, v \in {InitialVersion, NewVersion} : 
    (loadBalancer[s] = v) => \E t \in Servers : (loadBalancer[t] = v) /\ serverStatus[t] /= updating

SameVersion == 
  \A s, t \in Servers : 
    loadBalancer[s] = loadBalancer[t] => serverStatus[s] = serverStatus[t]

Termination == 
  <>(updatePhase = done)

THEOREM Spec => []ZeroDowntime
THEOREM Spec => []SameVersion
THEOREM Spec => Termination

=============================================================================