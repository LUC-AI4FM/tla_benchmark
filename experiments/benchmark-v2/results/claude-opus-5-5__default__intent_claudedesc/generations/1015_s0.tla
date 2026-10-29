---- MODULE VoucherLifecycle ----
EXTENDS Naturals, FiniteSets

CONSTANT V

VARIABLES vState, vlcState

vars == <<vState, vlcState>>

VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}
LifecycleStates == {"init", "working", "done"}

TypeOK ==
    /\ vState \in [V -> VoucherStates]
    /\ vlcState \in [V -> LifecycleStates]

Init ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]

Issue(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ UNCHANGED vars

Redeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Next ==
    \E v \in V :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

Spec == Init /\ [][Next]_vars

VConsistent ==
    \A v \in V :
        \/ vState[v] = "phantom" /\ vlcState[v] = "init"
        \/ vState[v] = "valid" /\ vlcState[v] = "working"
        \/ vState[v] = "redeemed" /\ vlcState[v] = "done"
        \/ vState[v] = "cancelled" /\ vlcState[v] = "done"

Terminal ==
    [][\A v \in V :
        /\ (vState[v] = "redeemed" => vState'[v] = "redeemed")
        /\ (vState[v] = "cancelled" => vState'[v] = "cancelled")]_vars

NoReturnToPhantom ==
    [][\A v \in V : vState[v] # "phantom" => vState'[v] # "phantom"]_vars

THEOREM Spec => [](TypeOK /\ VConsistent)
====