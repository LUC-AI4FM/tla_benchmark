```
MODULE VoucherLifeCycle

EXTENDS Integers, Sequences

CONSTANTS Vouchers, Actions
VARIABLES voucherState, lifeCycleMachine, validVouchers

Init ==
  /\ voucherState = [v \in Vouchers |-> "phantom"]
  /\ lifeCycleMachine = [v \in Vouchers |-> "initial"]
  /\ validVouchers = {}

Next ==
  /\ (voucherState' = voucherState) 
    \/ (\E v \in Vouchers : 
        /\ voucherState[v] = "phantom"
        /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
        /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "issued"])
  \/ (\E v \in Vouchers : 
      /\ voucherState[v] = "valid"
      /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "redeemed"])
  \/ (\E v \in Vouchers : 
      /\ voucherState[v] = "valid"
      /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
      /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "cancelled"])
  \/ (\E v \in Vouchers : 
      /\ voucherState[v] = "valid"
      /\ voucherState' = voucherState
      /\ lifeCycleMachine' = lifeCycleMachine)
  /\ validVouchers' = IF voucherState'["phantom"] \in validVouchers THEN validVouchers ELSE (validVouchers \cup {"phantom"}) 
  /\ UNCHANGED <<voucherState, lifeCycleMachine, validVouchers>>

TypeCorrectness == 
  /\ voucherState \in [Vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifeCycleMachine \in [Vouchers -> {"initial", "issued", "redeemed", "cancelled"}]

ConsistencyInvariant == 
  /\ \A v \in Vouchers : 
    (voucherState[v] = "phantom") <=> (lifeCycleMachine[v] = "initial")
  /\ \A v \in Vouchers : 
    (voucherState[v] = "valid") <=> (lifeCycleMachine[v] = "issued")
  /\ \A v \in Vouchers : 
    (voucherState[v] = "redeemed") <=> (lifeCycleMachine[v] = "redeemed")
  /\ \A v \in Vouchers : 
    (voucherState[v] = "cancelled") <=> (lifeCycleMachine[v] = "cancelled")

Spec == Init /\ [][Next]_<<voucherState, lifeCycleMachine, validVouchers>>
Fairness == SF_voucher(v \in Vouchers)(voucherState[v] = "valid" /\ lifeCycleMachine[v] = "issued")

THEOREM Spec => []<<TypeCorrectness /\ ConsistencyInvariant>> 
  /\ Spec => Fairness

END VoucherLifeCycle
```