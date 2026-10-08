------------------------------- MODULE RollingDeployment -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Servers \* A finite set of servers

VARIABLES 
    updating, \* Set of servers currently being updated
    available \* Set of servers currently available behind the load balancer

Init == /\ updating = {}
        /\ available = Servers

Next ==
    \/ /\ \E s \in (Servers \ updating) :
           \/ /\ updating' = updating \cup {s}
              /\ available' = available \ {s}
       \/ /\ \A s \in Servers :
              (s \notin updating => available'[s] = TRUE)
       \/ /\ \E s \in updating :
           \/ /\ updating' = updating \ {s}
              /\ available' = available \cup {s}
    \/ /\ updating' = updating
       /\ available' = available

Spec ==
    Init /\ [][Next]_<<updating, available>> /\ WF_next(<<updating, available>>)

WF_next(vars) == WF_vars(vars) /\ SF_vars(vars)
WF_vars(vars) ==
    WFair \A s \in Servers :
        \A p \in {1} :
            <\AA <<updating, available>> \in vars : s \notin updating>
             -> <>[]<<updating, available>> \in vars : s \in updating>>
SF_vars(vars) ==
    SFair \A s \in Servers :
        \A p \in {2} :
            <\AA <<updating, available>> \in vars : s \in updating>
             -> <>[]<<updating, available>> \in vars : s \notin updating>

Termination == <><><> /\ []<>(updating = {})

=============================================================================