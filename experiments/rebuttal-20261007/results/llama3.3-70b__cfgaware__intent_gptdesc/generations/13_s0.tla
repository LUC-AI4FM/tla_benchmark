--------------------------- MODULE Spec ---------------------------
EXTENDS Integers, TLC

CONSTANT Servers, NewVersion
VARIABLES version, updating, loadBalanced

Init ==
  /\ version = [s \in Servers |-> "old"]
  /\ updating = [s \in Servers |-> FALSE]
  /\ loadBalanced = Servers

Update(s) ==
  /\ updating' = [updating EXCEPT ![s] = TRUE]
  /\ version' = [version EXCEPT ![s] = "updating"]
  /\ loadBalanced' = loadBalanced \ {s}
  /\ UNCHANGED <<version, updating, loadBalanced>>

FinishUpdate(s) ==
  /\ updating' = [updating EXCEPT ![s] = FALSE]
  /\ version' = [version EXCEPT ![s] = NewVersion]
  /\ loadBalanced' = loadBalanced \cup {s}
  /\ UNCHANGED <<version, updating, loadBalanced>>

Orchestrate ==
  /\ \E s \in Servers : updating[s] = FALSE
  /\ version' = version
  /\ updating' = [updating EXCEPT ![s] = TRUE]
  /\ loadBalanced' = loadBalanced \ {s}
  /\ UNCHANGED <<version, updating, loadBalanced>>

Next ==
  \/ \E s \in Servers : 
    /\ version[s] = "old"
    /\ updating[s] = FALSE
    /\ Update(s)
  \/ \E s \in Servers : 
    /\ version[s] = "updating"
    /\ FinishUpdate(s)
  \/ Orchestrate

Spec ==
  Init /\ [][Next]_<<version, updating, loadBalanced>>

THEOREM Spec => [](\A s, t \in loadBalanced : version[s] = version[t])
THEOREM Spec => <>[](~\E s \in Servers : updating[s] = TRUE)
THEOREM Spec => <>(\A s \in Servers : version[s] = NewVersion)

====================================================================