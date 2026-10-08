------------------------------ MODULE RollingDeploy ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME N \in Nat \* Number of servers
ASSUME N = 3

(*
  Servers are identified as integers 1..N.
  Each server status is one of: "Old", "Updating", "New".
  LB is the set of servers currently behind the load balancer.
  switched indicates whether the LB has been switched to the "New" cohort.
*)

VARIABLES
  status,   \* function Servers -> {"Old","Updating","New"}
  LB,       \* subset of Servers
  switched  \* boolean

Servers == 1..N

OldSet == { s \in Servers : status[s] = "Old" }
UpdatingSet == { s \in Servers : status[s] = "Updating" }
NewSet == { s \in Servers : status[s] = "New" }

NoOneUpdating == Cardinality(UpdatingSet) = 0

vars == << status, LB, switched >>

Init ==
  /\ status = [ s \in Servers |-> "Old" ]
  /\ LB = Servers
  /\ switched = FALSE

(*
  StartUpdate merges "remove from LB" (when pre-switch) and "enter Updating".
  - Before switch: must remove a server from LB while leaving at least one in LB (Cardinality(LB) >= 2).
  - After switch: all remaining Old servers are already out of LB.
  Only one server may be in Updating at a time (NoOneUpdating).
*)
StartUpdate(s) ==
  /\ s \in Servers
  /\ NoOneUpdating
  /\ status[s] = "Old"
  /\ IF switched
        THEN s \notin LB
        ELSE /\ s \in LB
             /\ Cardinality(LB) >= 2
  /\ status' = [status EXCEPT ![s] = "Updating"]
  /\ LB' = IF switched THEN LB ELSE (LB \ {s})
  /\ UNCHANGED switched

(*
  FinishUpdate completes an Updating server to New.
  After switch, newly New servers are added to LB to keep LB on the New cohort.
*)
FinishUpdate(s) ==
  /\ s \in Servers
  /\ status[s] = "Updating"
  /\ status' = [status EXCEPT ![s] = "New"]
  /\ LB' = IF switched THEN (LB \cup {s}) ELSE LB
  /\ UNCHANGED switched

(*
  SwitchToNew performs the atomic LB switch to the New cohort once at least two servers are New.
*)
SwitchToNew ==
  /\ ~switched
  /\ Cardinality(NewSet) >= 2
  /\ switched' = TRUE
  /\ LB' = NewSet
  /\ UNCHANGED status

Next ==
  \/ (\E s \in Servers : StartUpdate(s))
  \/ (\E s \in Servers : FinishUpdate(s))
  \/ SwitchToNew

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E s \in Servers : StartUpdate(s))
  /\ WF_vars(\E s \in Servers : FinishUpdate(s))
  /\ WF_vars(SwitchToNew)

(*
  Safety invariants required by the problem statement.
  - ZeroDowntime: the LB always contains at least one server not mid-update.
  - SameVersion: all servers behind the LB always run the same version as each other.
    (Together with ZeroDowntime, this implies LB is never empty and contains
     only Old or only New servers at any time.)
*)
ZeroDowntime ==
  \E s \in LB : status[s] # "Updating"

SameVersion ==
  \E v \in {"Old","New"} : \A s \in LB : status[s] = v

(*
  Strengthening invariants used by the construction.
*)
NoUpdatingInLB == \A s \in LB : status[s] # "Updating"
AtMostOneUpdating == Cardinality(UpdatingSet) <= 1

Safety == ZeroDowntime /\ SameVersion

(*
  Liveness/termination: eventually all servers are New.
*)
AllUpdated == \A s \in Servers : status[s] = "New"
Termination == <>AllUpdated

=============================================================================