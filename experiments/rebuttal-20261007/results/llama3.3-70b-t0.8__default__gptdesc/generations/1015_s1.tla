```
MODULE VoucherLifeCycle

EXTENDS Integers, TLC

CONSTANTS Vouchers, Actions
VARIABLES voucherState, lifeCycleMachine

Init == (
  /\ voucherState = [v \in Vouchers |-> "phantom"]
  /\ lifeCycleMachine = [v \in Vouchers |-> "initial"]
)

TypeCorrectness == (
  /\ voucherState \in [Vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifeCycleMachine \in [Vouchers -> {"initial", "issued", "redeemed", "cancelled"}]
)

ConsistencyInvariant == (
  /\ \A v \in Vouchers : 
    /\ (voucherState[v] = "phantom") => (lifeCycleMachine[v] = "initial")
    /\ (voucherState[v] = "valid") => (lifeCycleMachine[v] = "issued")
    /\ (voucherState[v] = "redeemed") => (lifeCycleMachine[v] = "redeemed")
    /\ (voucherState[v] = "cancelled") => (lifeCycleMachine[v] = "cancelled")
)

Issue(v) == (
  /\ voucherState[v] = "phantom"
  /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
  /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "issued"]
  /\ UNCHANGED << >>
)

Redeem(v) == (
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
  /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "redeemed"]
  /\ UNCHANGED << >>
)

Cancel(v) == (
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
  /\ lifeCycleMachine' = [lifeCycleMachine EXCEPT ![v] = "cancelled"]
  /\ UNCHANGED << >>
)

Transfer(v) == (
  /\ voucherState[v] = "valid"
  /\ voucherState' = voucherState
  /\ lifeCycleMachine' = lifeCycleMachine
  /\ UNCHANGED << >>
)

Next == (
  \E v \in Vouchers : 
    Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)
)

Spec == Init /\ [][Next]_<<voucherState, lifeCycleMachine>>

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []ConsistencyInvariant

Fairness == WF_v(VoucherLifeCycle)(Issue(v)) /\ WF_v(VoucherLifeCycle)(Redeem(v)) /\ WF_v(VoucherLifeCycle)(Cancel(v))

END VoucherLifeCycle
```