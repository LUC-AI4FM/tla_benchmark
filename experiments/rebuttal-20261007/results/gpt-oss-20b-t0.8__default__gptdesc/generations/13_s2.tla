MODULE RollingDeployment
EXTENDS Naturals

CONSTANTS SERVERS \* Set of server identifiers

VARIABLES serverState, inLB, pending, current, coordinatorStep

ServerStates == {"idle","updating","updated"}

AtLeastOneInLB == ∃ s ∈ SERVERS : inLB[s] = TRUE
AllUpdated        == ∀ s ∈ SERVERS : serverState[s] = "updated"
TypeInvariant    ==  serverState \in [SERVERS -> ServerStates]
                    /\ inLB \in [SERVERS -> BOOLEAN]
                    /\ pending \subseteq SERVERS
                    /\ current \in SERVERS \cup {⊥}
                    /\ coordinatorStep ∈ {"idle","removing","waiting"}

Init ==
  /\ serverState = [s \in SERVERS |-> "idle"]
  /\ inLB       = [s \in SERVERS |-> TRUE]
  /\ pending    = SERVERS
  /\ current    = ⊥
  /\ coordinatorStep = "idle"

CoordinatorPick ==
  ∃ s ∈ pending :
    /\ coordinatorStep = "idle"
    /\ current'        = s
    /\ pending'        = pending \ {s}
    /\ coordinatorStep'= "removing"
    /\ UNCHANGED << serverState, inLB >>

RemoveServer ==
  /\ coordinatorStep = "removing"
  /\ inLB'        = [inLB EXCEPT ![current] = FALSE]
  /\ serverState' = [serverState EXCEPT ![current] = "updating"]
  /\ coordinatorStep'= "waiting"
  /\ UNCHANGED << current >>

UpdateComplete ==
  /\ coordinatorStep = "waiting"
  /\ current \in SERVERS
  /\ serverState[current] = "updating"
  /\ serverState'[current] = "updated"
  /\ UNCHANGED << inLB, pending, current, coordinatorStep >>

RestoreServer ==
  /\ coordinatorStep = "waiting"
  /\ current \in SERVERS
  /\ serverState[current] = "updated"
  /\ inLB'        = [inLB EXCEPT ![current] = TRUE]
  /\ coordinatorStep'= "idle"
  /\ current'     = ⊥
  /\ UNCHANGED << pending, serverState >>

Idle ==
  /\ pending    = ∅
  /\ current    = ⊥
  /\ coordinatorStep = "idle"
  /\ UNCHANGED << serverState, inLB >>

Next == CoordinatorPick \/ RemoveServer \/ UpdateComplete \/ RestoreServer \/ Idle

Terminated ==
  /\ pending   = ∅
  /\ current   = ⊥
  /\ coordinatorStep = "idle"
  /\ AllUpdated

Spec ==
  Init
  /\ [][Next]_<< serverState, inLB, pending, current, coordinatorStep >>
  /\ WF_vars[CoordinatorPick]
  /\ WF_vars[RemoveServer]
  /\ WF_vars[UpdateComplete]
  /\ WF_vars[RestoreServer]
  /\ <> Terminated

Safety == [] AtLeastOneInLB

=============================================================================