------------------------------- MODULE VoucherLifecycle -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    Vouchers  \* The set of all vouchers

VARIABLES 
    voucherState  \* Maps each voucher to its state: "phantom", "valid", "redeemed", or "cancelled"

Init == 
    /\ voucherState \in [Vouchers -> {"phantom"}]

Next ==
    \/ \/ \E v \in Vouchers : 
            /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
            /\ voucherState[v] = "phantom"
       \/ \/ \E v \in Vouchers :
                /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
                /\ voucherState[v] = "valid"
          \/ \E v \in Vouchers :
                /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
                /\ voucherState[v] = "valid"
          \/ \A v \in Vouchers :
                voucherState'[v] = voucherState[v]

TypeCorrectness ==
    \A v \in Vouchers : voucherState[v] \in {"phantom", "valid", "redeemed", "cancelled"}

ConsistencyInvariant ==
    TRUE  \* Placeholder for any additional consistency invariants

Spec == 
    /\ Init
    /\ [][Next]_<<voucherState>>
    /\ WF_next(<<voucherState>>)

WF_next(vars) == 
    \/ STAY_put(vars)
    \/ TRANSFER_put(vars)

STAY_put(vars) ==
    \A v \in Vouchers : vars'[v] = vars[v]

TRANSFER_put(vars) ==
    \E v \in Vouchers :
        /\ vars'[v] = "valid"
        /\ vars[v] = "valid"

=============================================================================