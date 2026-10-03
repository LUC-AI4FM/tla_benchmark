------------------------------- MODULE VoucherLifecycle -------------------------------

CONSTANTS V \* The set of all vouchers

VStates == {"phantom", "valid", "redeemed", "cancelled"}

VTypeOK == \A v \in V: v.state \in VStates /\ (v.state = "phantom" => v.action = "issue") 
           /\ (v.state = "valid" => v.action \in {"transfer", "redeem", "cancel"})
           /\ (v.state \in {"redeemed", "cancelled"} => v.action = "")

VConsistent == \A v \in V: \/ v.state = "phantom" /\ v.action = "issue"
                             \/ v.state = "valid" /\ v.action \in {"transfer", "redeem", "cancel"}
                             \/ v.state = "redeemed" /\ v.action = ""
                             \/ v.state = "cancelled" /\ v.action = ""

VNext == [v \in V |-> 
            CASE v.state = "phantom" -> IF v.action = "issue" THEN [state |-> "valid", action |-> "transfer"]
                                       ELSE [state |-> "phantom", action |-> "issue"]
             [] v.state = "valid" -> IF v.action = "redeem" THEN [state |-> "redeemed", action |-> ""]
                                      [] v.action = "cancel" THEN [state |-> "cancelled", action |-> ""]
                                      [] v.action = "transfer" THEN [state |-> "valid", action |-> "transfer"]
                                      ELSE [state |-> "valid", action |-> "transfer"]
             [] v.state \in {"redeemed", "cancelled"} -> [state |-> v.state, action |-> v.action]]

VInit == [v \in V |-> [state |-> "phantom", action |-> "issue"]]

VSpec == /\ TYPEOK
         /\ INIT = VInit
         /\ NEXTSTATE = (\E v2 \in [V -> [state: VStates, action: {"issue", "transfer", "redeem", ""}]]:
                           \A v \in V: v2[v] = VNext[v])
         /\ []<>(\A v \in V: VConsistent[v])

=============================================================================