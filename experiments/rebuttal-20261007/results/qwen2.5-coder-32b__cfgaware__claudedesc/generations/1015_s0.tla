---- MODULE VoucherLifecycle ----

CONSTANTS V \* The set of vouchers

VARIABLES vState, vlcState \* State variables for vouchers

\* Possible states for vState and vlcState
STATE == {"phantom", "valid", "redeemed", "cancelled"}
LC_STATE == {"init", "working", "done"}

\* Initial predicate
Init == 
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

\* Action: Issue
Issue(v) ==
  \/ vState[v] = "phantom" /\ vlcState[v] = "init"
     /\ vState' = [vState EXCEPT ![v] = "valid"]
     /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
  \/ UNCHANGED <<vState, vlcState>>

\* Action: Transfer
Transfer(v) ==
  \/ vState[v] = "valid"
     /\ UNCHANGED <<vState, vlcState>>
  \/ UNCHANGED <<vState, vlcState>>

\* Action: Redeem
Redeem(v) ==
  \/ vState[v] = "valid" /\ vlcState[v] = "working"
     /\ vState' = [vState EXCEPT ![v] = "redeemed"]
     /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  \/ UNCHANGED <<vState, vlcState>>

\* Action: Cancel
Cancel(v) ==
  \/ vState[v] = "valid" /\ vlcState[v] = "working"
     /\ vState' = [vState EXCEPT ![v] = "cancelled"]
     /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  \/ UNCHANGED <<vState, vlcState>>

\* Next-state relation
VNext ==
  \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

\* Type invariants
VTypeOK == 
  /\ vState \in [V -> STATE]
  /\ vlcState \in [V -> LC_STATE]

\* Consistency invariant
VConsistent ==
  \A v \in V :
    (vState[v] = "phantom" => vlcState[v] = "init")
    \/ (vState[v] = "valid" => vlcState[v] = "working")
    \/ (vState[v] \in {"redeemed", "cancelled"} => vlcState[v] = "done")

\* Temporal specification
VSpec ==
  Init /\ [][VNext]_<<vState, vlcState>>

THEOREM VSpec => []VTypeOK /\ []VConsistent

====