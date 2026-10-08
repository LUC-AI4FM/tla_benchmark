---------------------------- MODULE VoucherLifecycle ----------------------------

CONSTANTS V \* The set of all vouchers

VStates == {"not-yet-issued", "issued/usable", "consumed", "invalidated"}
LCMStates == {"not-started", "active", "completed"}

VTypeOK == \A v \in V: /\ vc[v] \in VStates
                 /\ vlcm[v] \in LCMStates

VConsistent == \A v \in V:
    CASE vc[v] = "not-yet-issued" -> vlcm[v] = "not-started"
    [] vc[v] = "issued/usable"  -> vlcm[v] = "active"
    [] vc[v] \in {"consumed", "invalidated"} -> vlcm[v] = "completed"

VSpec == INSTANCE SpecWhere ==
    VARIABLES vc, vlcm
    VARIABLE v2 \* A placeholder variable for any voucher

    DEF Init == /\ vc = [v \in V |-> "not-yet-issued"]
                /\ vlcm = [v \in V |-> "not-started"]

    DEF Issue(v) == /\ vc[v] = "not-yet-issued"
                    /\ vlcm[v] = "not-started"
                    /\ vc' = [vc EXCEPT ![v] = "issued/usable"]
                    /\ vlcm' = [vlcm EXCEPT ![v] = "active"]

    DEF Transfer(v) == /\ vc[v] = "issued/usable"
                       /\ vlcm[v] = "active"
                       /\ vc' = vc
                       /\ vlcm' = vlcm

    DEF Redeem(v) == /\ vc[v] = "issued/usable"
                     /\ vlcm[v] = "active"
                     /\ vc' = [vc EXCEPT ![v] = "consumed"]
                     /\ vlcm' = [vlcm EXCEPT ![v] = "completed"]

    DEF Cancel(v) == /\ vc[v] = "issued/usable"
                    /\ vlcm[v] = "active"
                    /\ vc' = [vc EXCEPT ![v] = "invalidated"]
                    /\ vlcm' = [vlcm EXCEPT ![v] = "completed"]

    DEF Next ==
        \/ \E v \in V: Issue(v)
        \/ \E v \in V: Transfer(v)
        \/ \E v \in V: Redeem(v)
        \/ \E v \in V: Cancel(v)

    DEF Spec == Init /\ [][Next]_<<vc, vlcm>>

    DEF Inv ==
        /\ VTypeOK
        /\ VConsistent

    DEF Live ==
        <>[](\E v \in V: Issue(v))
        /\ <>[](\E v \in V: Redeem(v) \/ Cancel(v))

THEOREM Spec => []Inv

THEOREM Spec => Live

=============================================================================