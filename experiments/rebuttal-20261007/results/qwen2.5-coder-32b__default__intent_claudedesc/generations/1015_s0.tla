------------------------------- MODULE VoucherLifecycle -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Vouchers \* A finite set of vouchers

VARIABLES 
    states \* Maps each voucher to its state: "phantom", "valid", "redeemed", or "cancelled"

Init == 
    /\ states \in [Vouchers -> {"phantom"}]

Next ==
    \/ \/ \E v \in Vouchers : states' = [states EXCEPT ![v] = "valid"]
       /\ states[v] = "phantom"
    \/ \/ \E v \in Vouchers : states' = states
       /\ states[v] = "valid"
    \/ \/ \E v \in Vouchers : states' = [states EXCEPT ![v] = "redeemed"]
       /\ states[v] = "valid"
    \/ \/ \E v \in Vouchers : states' = [states EXCEPT ![v] = "cancelled"]
       /\ states[v] = "valid"

Spec ==
    /\ Init
    /\ [][Next]_<<states>>

Invariant ==
    \A v \in Vouchers :
        \/ states[v] = "phantom"
        \/ states[v] = "valid"
        \/ states[v] = "redeemed"
        \/ states[v] = "cancelled"

=============================================================================