------------------------------- MODULE VoucherLifecycle -------------------------------

CONSTANTS V \* The set of all vouchers

VTypeOK == \A v \in V : v \in {"phantom", "valid", "redeemed", "cancelled"}

VConsistent ==
    /\ \A v \in V : \/ v = "phantom"
                       \/ v = "valid"
                       \/ v = "redeemed"
                       \/ v = "cancelled"
    /\ \A v1, v2 \in V : v1 # v2 => <<v1, v2>> \notin {"phantom", "valid"} \X {"redeemed", "cancelled"}

VSpec ==
    VARIABLES state
    INIT == state = [v \in V |-> "phantom"]
    TRANS ==
        \/ /\ \E v \in V : state[v] = "phantom" /\ state' = [state EXCEPT ![v] = "valid"]
        \/ /\ \E v \in V : state[v] = "valid" /\ state' = [state EXCEPT ![v] = "redeemed"]
        \/ /\ \E v \in V : state[v] = "valid" /\ state' = [state EXCEPT ![v] = "cancelled"]
        \/ /\ \E v \in V : state[v] = "valid" /\ state' = state
    SPECIFICATION INIT /\ [][TRANS]_<<state>> /\ WF_next(TRANS, <<state>>) /\ VConsistent

=============================================================================