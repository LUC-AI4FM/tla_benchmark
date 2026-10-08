```
MODULE VoucherLifecycle

EXTENDS Integers, FiniteSets

CONSTANTS Vouchers
VARIABLES voucherState, lifecycleState

Init ==
  /\ voucherState \in [Vouchers -> {"not-yet-issued", "issued", "consumed", "cancelled"}]
  /\ lifecycleState \in [Vouchers -> {"not-started", "active", "completed"}]
  /\ voucherState = [v \in Vouchers |-> "not-yet-issued"]
  /\ lifecycleState = [v \in Vouchers |-> "not-started"]

Next ==
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "not-yet-issued"
      /\ voucherState' = [voucherState EXCEPT ![v] = "issued"]
      /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "active"]
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "issued"
      /\ lifecycleState[v] = "active"
      /\ voucherState' = voucherState
      /\ lifecycleState' = lifecycleState
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "issued"
      /\ lifecycleState[v] = "active"
      /\ voucherState' = [voucherState EXCEPT ![v] = "consumed"]
      /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]
  \/ \E v \in Vouchers :
      /\ voucherState[v] = "issued"
      /\ lifecycleState[v] = "active"
      /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
      /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]
  \/ voucherState' = voucherState
  /\ lifecycleState' = lifecycleState

Spec ==
  Init /\ [][Next]_<<voucherState, lifecycleState>>

Invariant1 == 
  /\ voucherState \in [Vouchers -> {"not-yet-issued", "issued", "consumed", "cancelled"}]
  /\ lifecycleState \in [Vouchers -> {"not-started", "active", "completed"}]

Invariant2 == 
  \A v \in Vouchers :
    (voucherState[v] = "not-yet-issued" => lifecycleState[v] = "not-started")
    /\ (voucherState[v] = "issued" => lifecycleState[v] = "active")
    /\ (voucherState[v] \in {"consumed", "cancelled"} => lifecycleState[v] = "completed")

Invariant3 == 
  \A v \in Vouchers :
    ~(voucherState[v] = "consumed" /\ voucherState[v] = "cancelled")

THEOREM Spec => []Invariant1
THEOREM Spec => []Invariant2
THEOREM Spec => []Invariant3

Fairness == 
  \A v \in Vouchers :
    <>(voucherState[v] = "not-yet-issued" /\ voucherState'[v] = "issued")
    /\ <>(voucherState[v] = "issued" /\ lifecycleState[v] = "active" /\ (voucherState'[v] = "consumed" \/ voucherState'[v] = "cancelled"))

THEOREM Spec => []Fairness
```