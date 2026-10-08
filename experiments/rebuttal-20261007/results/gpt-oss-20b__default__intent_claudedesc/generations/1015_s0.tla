MODULE VoucherLifecycle
EXTENDS Naturals

CONSTANTS VOUCHERS

VARIABLES voucherState, lifecycleState

VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}
LifecycleStates == {"unstarted", "in-progress", "completed"}

Init ==
  /\ voucherState \in [VOUCHERS -> VoucherStates]
  /\ lifecycleState \in [VOUCHERS -> LifecycleStates]
  /\ \A v \in VOUCHERS : voucherState[v] = "phantom" /\ lifecycleState[v] = "unstarted"

Issue(v) ==
  /\ v \in VOUCHERS
  /\ voucherState[v] = "phantom"
  /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "in-progress"]

Transfer(v) ==
  /\ v \in VOUCHERS
  /\ voucherState[v] = "valid"
  /\ voucherState' = voucherState
  /\ lifecycleState' = lifecycleState

Redeem(v) ==
  /\ v \in VOUCHERS
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

Cancel(v) ==
  /\ v \in VOUCHERS
  /\ voucherState[v] = "valid"
  /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
  /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

Next == 
  \E v \in VOUCHERS : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

SafetyInvariant ==
  \A v \in VOUCHERS :
    (voucherState[v] = "phantom" /\ lifecycleState[v] = "unstarted") \/
    (voucherState[v] = "valid" /\ lifecycleState[v] = "in-progress") \/
    ((voucherState[v] = "redeemed" \/ voucherState[v] = "cancelled") /\ lifecycleState[v] = "completed")

Spec == Init /\ [][Next]_<<voucherState, lifecycleState>> /\ SafetyInvariant