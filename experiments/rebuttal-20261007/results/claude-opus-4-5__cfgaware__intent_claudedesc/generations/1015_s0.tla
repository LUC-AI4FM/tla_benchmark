---------------------------- MODULE voucher ----------------------------

EXTENDS Naturals

CONSTANT V

VARIABLES voucher_state, lifecycle_state

v2 == <<voucher_state, lifecycle_state>>

VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}
LifecycleStates == {"unstarted", "in_progress", "completed"}

VTypeOK == 
    /\ voucher_state \in [V -> VoucherStates]
    /\ lifecycle_state \in [V -> LifecycleStates]

VConsistent ==
    \A v \in V :
        /\ (voucher_state[v] = "phantom") <=> (lifecycle_state[v] = "unstarted")
        /\ (voucher_state[v] = "valid") <=> (lifecycle_state[v] = "in_progress")
        /\ (voucher_state[v] \in {"redeemed", "cancelled"}) <=> (lifecycle_state[v] = "completed")

VInit ==
    /\ voucher_state = [v \in V |-> "phantom"]
    /\ lifecycle_state = [v \in V |-> "unstarted"]

Issue(v) ==
    /\ voucher_state[v] = "phantom"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "valid"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "in_progress"]

Transfer(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = voucher_state
    /\ lifecycle_state' = lifecycle_state

Redeem(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "redeemed"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "completed"]

Cancel(v) ==
    /\ voucher_state[v] = "valid"
    /\ voucher_state' = [voucher_state EXCEPT ![v] = "cancelled"]
    /\ lifecycle_state' = [lifecycle_state EXCEPT ![v] = "completed"]

VNext ==
    \E v \in V :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

VSpec == VInit /\ [][VNext]_v2

==========================================================================