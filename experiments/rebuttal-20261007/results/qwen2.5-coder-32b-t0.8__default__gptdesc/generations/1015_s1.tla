------------------------------- MODULE VoucherLifecycle -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Vouchers

VARIABLES
    states

TYPE_OK == \A v \in Vouchers: states[v] \in {"phantom", "valid", "redeemed", "cancelled"}

Init == 
    /\ states = [v \in Vouchers |-> "phantom"]

Next ==
    \/ \E v \in Vouchers: states'[v] = "valid" /\ \A u \in Vouchers \ {v}: states'[u] = states[u]
    \/ \E v \in Vouchers: states[v] = "valid" => (states'[v] = states[v] \/ (\E u \in Vouchers \ {v}: states'[u] = states[u] /\ states'[v] = "redeemed"))
    \/ \E v \in Vouchers: states[v] = "valid" => (states'[v] = states[v] \/ (\E u \in Vouchers \ {v}: states'[u] = states[u] /\ states'[v] = "cancelled"))

Consistency ==
    /\ TYPE_OK
    /\ \A v \in Vouchers: states[v] = "phantom" => ~(\E u \in Vouchers \ {v}: states[u] = "valid")
    /\ \A v \in Vouchers: states[v] \in {"redeemed", "cancelled"} => ~(\E u \in Vouchers \ {v}: states[u] = "valid")

Spec ==
    /\ Init
    /\ [][Next]_<<states>>
    /\ <>[Consistency]_<<states>>

WF_next == 
    WF_vars(Next, <<states>>)

=============================================================================