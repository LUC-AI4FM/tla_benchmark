------------------------------- MODULE VoucherLifecycle -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS V \* A finite set of vouchers

VARIABLES vState, vlcState \* State variables for vouchers

(* --algorithm VoucherLifecycle

variables 
    vState = [v \in V |-> "phantom"],
    vlcState = [v \in V |-> "init"];

fair process (ALL) = 1:
    while TRUE do
        either
            /\ \/ \E v \in V : vState[v] = "phantom" /\ vlcState[v] = "init"
            /\ vState' = [vState EXCEPT ![v] = "valid"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
        or
            /\ \/ \E v \in V : vState[v] = "valid" 
            /\ vState' = vState
            /\ vlcState' = vlcState
        or
            /\ \/ \E v \in V : vState[v] = "valid" /\ vlcState[v] = "working"
            /\ vState' = [vState EXCEPT ![v] = "redeemed"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
        or
            /\ \/ \E v \in V : vState[v] = "valid" /\ vlcState[v] = "working"
            /\ vState' = [vState EXCEPT ![v] = "cancelled"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
        end either;
    od;

end algorithm *)

VConsistent == \A v \in V : 
    \/ (vState[v] = "phantom" /\ vlcState[v] = "init")
    \/ (vState[v] = "valid" /\ vlcState[v] = "working")
    \/ ((vState[v] = "redeemed" \/ vState[v] = "cancelled") /\ vlcState[v] = "done")

VTypeOK == \A v \in V : 
    \/ vState[v] \in {"phantom", "valid", "redeemed", "cancelled"}
    /\ vlcState[v] \in {"init", "working", "done"}

Init == (vState = [v \in V |-> "phantom"]) /\ (vlcState = [v \in V |-> "init"])

Next == \/ \E v \in V : 
            vState[v] = "phantom" /\ vlcState[v] = "init"
            /\ vState' = [vState EXCEPT ![v] = "valid"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
         \/ \E v \in V : 
            vState[v] = "valid" 
            /\ vState' = vState
            /\ vlcState' = vlcState
         \/ \E v \in V : 
            vState[v] = "valid" /\ vlcState[v] = "working"
            /\ vState' = [vState EXCEPT ![v] = "redeemed"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
         \/ \E v \in V : 
            vState[v] = "valid" /\ vlcState[v] = "working"
            /\ vState' = [vState EXCEPT ![v] = "cancelled"]
            /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Spec == Init /\ [][Next]_<<vState, vlcState>> /\ WF_next(<<vState, vlcState>>)

THEOREM Spec => []VTypeOK /\ []VConsistent

=============================================================================