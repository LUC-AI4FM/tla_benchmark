```
MODULE VoucherLifeCycle

EXTENDS Integers, FiniteSets

CONSTANTS Vouchers, Actions
VARIABLES voucherState, lifeCycleMachine, currentAction

Init ==
  /\ voucherState \in [Vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifeCycleMachine \in [Vouchers -> {"new", "issued", "transferred", "redeemed", "cancelled"}]
  /\ currentAction = "none"
  /\ forall v \in Vouchers : voucherState[v] = "phantom"

Next ==
  /\ (currentAction = "issue" /\ E v \in Vouchers : 
        voucherState' = [voucherState EXCEPT ![v] = "valid"] 
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "issued"])
    \/ (currentAction = "transfer" /\ E v \in Vouchers :
        voucherState' = voucherState
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "transferred"]
      /\ voucherState[v] = "valid")
    \/ (currentAction = "redeem" /\ E v \in Vouchers : 
        voucherState' = [voucherState EXCEPT ![v] = "redeemed"] 
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "redeemed"])
    \/ (currentAction = "cancel" /\ E v \in Vouchers :
        voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "cancelled"])
    \/ (currentAction = "none")
  /\ currentAction' = "none"

ConsistencyInvariant ==
  forall v \in Vouchers :
    voucherState[v] = "valid" => lifeCycleMachine[v] \in {"issued", "transferred"}
  /\ voucherState[v] = "redeemed" => lifeCycleMachine[v] = "redeemed"
  /\ voucherState[v] = "cancelled" => lifeCycleMachine[v] = "cancelled"

TypeCorrectness ==
  voucherState \in [Vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifeCycleMachine \in [Vouchers -> {"new", "issued", "transferred", "redeemed", "cancelled"}]

Spec ==
  Init /\ [][Next]_<<voucherState, lifeCycleMachine, currentAction>>
  /\ WF_(currentAction = "issue")(Next)
  /\ WF_(currentAction = "transfer")(Next)
  /\ WF_(currentAction = "redeem")(Next)
  /\ WF_(currentAction = "cancel")(Next)

THEOREM Spec => []<<TypeCorrectness /\ ConsistencyInvariant>>
```
Note: The above code is a direct translation of the given system description into TLA+ and may need to be adjusted based on specific requirements or constraints not mentioned in the problem statement.