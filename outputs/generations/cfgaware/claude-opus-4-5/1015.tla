---------------------------- MODULE voucher ----------------------------

EXTENDS Naturals

CONSTANT V

VARIABLES voucher_state, lifecycle_state

v2 == <<voucher_state, lifecycle_state>>

VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

LifecycleStates == {"pre_issue", "active", "terminal"}

VTypeOK == 
    /\ voucher_state \in [V -> VoucherStates]
    /\ lifecycle_state \in [V -> LifecycleStates]

VConsistent ==
    \A v \in V :
        /\ (voucher_state[v] = "phantom") => (lifecycle_state[v] = "pre_issue")
        /\ (voucher_state[v] = "valid") => (lifecycle_state[v] = "active")
        /\ (voucher_state[v] \in {"redeemed", "cancelled"}) => (lifecycle_state[v] = "terminal")

VInit ==
    /\ voucher_state = [v \in V |-> "phantom"]
    /\ lifecycle_state = [v \in V |-> "pre_issue"]

Issue(v) ==
    /\ voucher_state[v] = "phantom"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "valid"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "active"]

Redeem(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "redeemed"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "terminal"]

Cancel(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "cancelled"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "terminal"]

Transfer(v) ==
    /\ voucher_state[v] = "valid"
    /\ UNCHANGED <<voucher_state, lifecycle_state>>

VNext ==
    \E v \in V :
        \/ Issue(v)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ Transfer(v)

VSpec == VInit /\ [][VNext]_v2

THEOREM VSpec => [](VTypeOK /\ VConsistent)

==========================================================================