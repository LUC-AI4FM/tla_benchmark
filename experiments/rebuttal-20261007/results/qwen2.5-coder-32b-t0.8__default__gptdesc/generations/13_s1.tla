------------------------------- MODULE RollingDeployment -------------------------------

EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS 
    Servers \* A finite set of servers

VARIABLES 
    updating \* The server currently being updated
    available \* Set of servers currently serving requests
    coordinatorState \* State of the coordinator (Idle, Updating)

Init == /\ updating = << >>
        /\ available = Servers
        /\ coordinatorState = "Idle"

Next == \/ \E s \in available: 
              /\ coordinatorState = "Updating"
              /\ updating' = Append(updating, s)
              /\ available' = available \ {s}
              /\ coordinatorState' = "Updating"
          \/ /\ coordinatorState = "Updating"
             /\ Len(updating) > 0
             /\ updating' = Tail(updating)
             /\ available' = available \cup {Head(updating)}
             /\ coordinatorState' = "Idle"
          \/ /\ coordinatorState = "Idle"
             /\ updating' = updating
             /\ available' = available
             /\ coordinatorState' = "Updating"

Spec == Init /\ [][Next]_<<available, updating, coordinatorState>>

\* Safety invariants
Invariant1 == available \subseteq Servers
Invariant2 == updating \in Seq(Servers)

\* Liveness property: All servers are eventually updated and restored to availability
Termination == <>(/\ updating = << >>
                    /\ coordinatorState = "Idle"
                    /\ available = Servers)

WF_coordinator == WF_<<available, updating, coordinatorState>>_(coordinatorState = "Updating")

WF_serverUpdate == WF_<<available, updating, coordinatorState>>_(Len(updating) > 0)

CompleteSpec == Spec /\ Invariant1 /\ Invariant2 /\ Termination /\ WF_coordinator /\ WF_serverUpdate

=============================================================================