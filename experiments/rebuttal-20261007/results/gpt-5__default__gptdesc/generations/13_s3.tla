------------------------------ MODULE RollingDeploy ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    SERVERS, \* finite, non-empty set of servers
    MinAvail, \* minimum number of servers that must remain in the load balancer
    NONE      \* a distinguished value not in SERVERS

ASSUME
    /\ NONE \notin SERVERS
    /\ MinAvail \in Nat
    /\ MinAvail >= 1
    /\ Cardinality(SERVERS) >= 1
    /\ MinAvail < Cardinality(SERVERS)

VARIABLES
    lb,       \* set of servers currently in service behind the load balancer
    status,   \* function: server -> {"Old","Updating","New"}
    req,      \* function: server -> BOOLEAN (update requested)
    cst,      \* coordinator control state
    cur       \* current server under coordination or NONE

States == {"Old", "Updating", "New"}
CoordStates == {"Pick","Remove","Trigger","Wait","Restore","Done"}

vars == << lb, status, req, cst, cur >>

TypeOK ==
    /\ lb \subseteq SERVERS
    /\ status \in [SERVERS -> States]
    /\ req \in [SERVERS -> BOOLEAN]
    /\ cst \in CoordStates
    /\ cur \in SERVERS \cup {NONE}

AvailabilityOK ==
    Cardinality(lb) >= MinAvail

NoUpdateInLB ==
    \A i \in SERVERS: status[i] = "Updating" => i \notin lb

RequestImpliesOut ==
    \A i \in SERVERS: req[i] => i \notin lb

WaitImplies ==
    cst = "Wait" => /\ cur \in SERVERS /\ req[cur] /\ cur \notin lb

AllDone ==
    \A i \in SERVERS: status[i] = "New"

Inv ==
    /\ TypeOK
    /\ AvailabilityOK
    /\ NoUpdateInLB
    /\ RequestImpliesOut
    /\ WaitImplies

Init ==
    /\ lb = SERVERS
    /\ status = [i \in SERVERS |-> "Old"]
    /\ req = [i \in SERVERS |-> FALSE]
    /\ cst = "Pick"
    /\ cur = NONE

Pick ==
    /\ cst = "Pick"
    /\ IF \E i \in SERVERS: status[i] # "New" THEN
          /\ LET candidates == { i \in SERVERS : status[i] # "New" } IN
               cur' = CHOOSE i \in candidates: TRUE
          /\ cst' = "Remove"
       ELSE
          /\ cur' = NONE
          /\ cst' = "Done"
    /\ UNCHANGED << lb, status, req >>

Remove ==
    /\ cst = "Remove"
    /\ cur \in SERVERS
    /\ cur \in lb
    /\ Cardinality(lb \ {cur}) >= MinAvail
    /\ lb' = lb \ {cur}
    /\ cst' = "Trigger"
    /\ UNCHANGED << status, req, cur >>

Trigger ==
    /\ cst = "Trigger"
    /\ cur \in SERVERS
    /\ req' = [req EXCEPT ![cur] = TRUE]
    /\ cst' = "Wait"
    /\ UNCHANGED << lb, status, cur >>

Wait ==
    /\ cst = "Wait"
    /\ cur \in SERVERS
    /\ status[cur] = "New"
    /\ cst' = "Restore"
    /\ UNCHANGED << lb, status, req, cur >>

Restore ==
    /\ cst = "Restore"
    /\ cur \in SERVERS
    /\ lb' = lb \cup {cur}
    /\ req' = [req EXCEPT ![cur] = FALSE]
    /\ cur' = NONE
    /\ cst' = "Pick"
    /\ UNCHANGED status

StartUpdate(i) ==
    /\ i \in SERVERS
    /\ req[i]
    /\ i \notin lb
    /\ status[i] = "Old"
    /\ status' = [status EXCEPT ![i] = "Updating"]
    /\ UNCHANGED << lb, req, cst, cur >>

FinishUpdate(i) ==
    /\ i \in SERVERS
    /\ status[i] = "Updating"
    /\ status' = [status EXCEPT ![i] = "New"]
    /\ UNCHANGED << lb, req, cst, cur >>

ServerStep ==
    \E i \in SERVERS: StartUpdate(i) \/ FinishUpdate(i)

CoordinatorStep ==
    Pick \/ Remove \/ Trigger \/ Wait \/ Restore

Next ==
    CoordinatorStep \/ ServerStep

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorStep)
    /\ (\A i \in SERVERS: WF_vars(StartUpdate(i)))
    /\ (\A i \in SERVERS: WF_vars(FinishUpdate(i)))

Termination ==
    <>(cst = "Done" /\ AllDone)

=============================================================================