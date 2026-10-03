---------------------------- MODULE VoucherLifeCycle ----------------------------
EXTENDS Integers, TLC

CONSTANT V, v2
VARIABLES voucherState, lifeCycleMachine

TypeOK == voucherState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
           /\ lifeCycleMachine \in [v2 -> {"new", "issued", "transferred", "redeemed", "cancelled"}]

VTypeOK == TypeOK

ConsistencyInvariant ==
  \A v \in V : 
    IF voucherState[v] = "phantom" THEN lifeCycleMachine[v2] = "new"
    ELSE IF voucherState[v] = "valid" THEN lifeCycleMachine[v2] \in {"issued", "transferred"}
    ELSE IF voucherState[v] = "redeemed" THEN lifeCycleMachine[v2] = "redeemed"
    ELSE lifeCycleMachine[v2] = "cancelled"

VConsistent == ConsistencyInvariant

Next ==
  /\ TypeOK
  /\ \E v \in V :
      (voucherState' = [voucherState EXCEPT ![v] = "valid"]
        /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v2] = "issued"])
      \/ (voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
          /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v2] = "redeemed"])
      \/ (voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
          /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v2] = "cancelled"])
      \/ (voucherState' = voucherState
          /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v2] = "transferred"])

VSpec == VTypeOK /\ [][Next]_<<voucherState, lifeCycleMachine>>
=============================================================================