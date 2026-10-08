------------------------------- MODULE VoucherLifecycle -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS vouchers

VSTATE == {"phantom", "valid", "redeemed", "cancelled"}

VoucherState == [vouchers -> VSTATE]

Init == /\ VoucherState = [v \in vouchers |-> "phantom"]

Next ==
  \E v \in vouchers : 
    ( \/ /\ VoucherState' = [VoucherState EXCEPT ![v] = "valid"]
        \/ /\ VoucherState[v] = "valid"
           /\ VoucherState' = [VoucherState EXCEPT ![v] = "redeemed"]
        \/ /\ VoucherState[v] = "valid"
           /\ VoucherState' = [VoucherState EXCEPT ![v] = "cancelled"]
        \/ /\ VoucherState[v] = "valid"
           /\ VoucherState' = VoucherState
     )

TypeOK == \A v \in vouchers : VoucherState[v] \in VSTATE

Consistency ==
  \A v \in vouchers :
    \/ VoucherState[v] = "phantom"
    \/ VoucherState[v] = "valid"
    \/ VoucherState[v] = "redeemed"
    \/ VoucherState[v] = "cancelled"

Spec == 
  /\ Init
  /\ [][Next]_<<VoucherState>>
  /\ WF_next(<<VoucherState>>)

=====================================================================================