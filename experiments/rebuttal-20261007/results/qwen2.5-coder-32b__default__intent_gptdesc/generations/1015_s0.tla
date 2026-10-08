```tla
------------------------------- MODULE VoucherLifecycle -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Vouchers

VARIABLES BusinessStates, LifecycleStates

(* --algorithm VoucherLifecycle

variables 
    businessState = [v \in Vouchers |-> "not-yet-issued"],
    lifecycleState = [v \in Vouchers |-> "not-started"];

Init == /\ businessState \in [Vouchers -> {"not-yet-issued", "issued/usable", "consumed", "invalidated"}]
        /\ lifecycleState \in [Vouchers -> {"not-started", "active", "completed"}]
        /\ (\A v \in Vouchers: businessState[v] = "not-yet-issued" /\ lifecycleState[v] = "not-started")

Issue(v) == 
    /\ businessState[v] = "not-yet-issued"
    /\ lifecycleState[v] = "not-started"
    /\ businessState' = [businessState EXCEPT ![v] = "issued/usable"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "active"]

Transfer(v) ==
    /\ businessState[v] = "issued/usable"
    /\ lifecycleState[v] = "active"
    /\ UNCHANGED <<businessState, lifecycleState>>

Redeem(v) == 
    /\ businessState[v] = "issued/usable"
    /\ lifecycleState[v] = "active"
    /\ businessState' = [businessState EXCEPT ![v] = "consumed"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

Cancel(v) == 
    /\ businessState[v] = "issued/usable"
    /\ lifecycleState[v] = "active"
    /\ businessState' = [businessState EXCEPT ![v] = "invalidated"]
    /\ lifecycleState' = [lifecycleState EXCEPT ![v] = "completed"]

Next ==
    \/ \E v \in Vouchers: Issue(v)
    \/ \E v \in Vouchers: Transfer(v)
    \/ \E v \in Vouchers: Redeem(v)
    \/ \E v \in Vouchers: Cancel(v)

Spec == Init /\ [][Next]_<<businessState, lifecycleState>>

Invariant1 ==
    (\A v \in Vouchers: businessState[v] \in {"not-yet-issued", "issued/usable", "consumed", "invalidated"})

Invariant2 ==
    (\A v \in Vouchers: lifecycleState[v] \in {"not-started", "active", "completed"})

Invariant3 ==
    (\A v \in Vouchers:
        \/ (businessState[v] = "not-yet-issued" /\ lifecycleState[v] = "not-started")
        \/ (businessState[v] = "issued/usable" /\ lifecycleState[v] = "active")
        \/ ((businessState[v] = "consumed" \/ businessState[v] = "invalidated") /\ lifecycleState[v] = "completed"))

Invariant4 ==
    (\A v \in Vouchers: 
        (lifecycleState[v] = "completed") => (businessState[v] = "consumed" \/ businessState[v] = "invalidated"))

Invariant5 ==
    (\A v \in Vouchers:
        (businessState[v] = "issued/usable") => (lifecycleState[v] = "active"))

Liveness1 ==
    <>(\E v \in Vouchers: Issue(v))

Liveness2 ==
    <>(\E v \in Vouchers: Redeem(v) \/ Cancel(v))

Termination ==
    [](businessState' = businessState)

Spec == Spec /\ Invariant1 /\ Invariant2 /\ Invariant3 /\ Invariant4 /\ Invariant5 /\ Liveness1 /\ Liveness2

 fairness assumptions
WF_spec == WF_vars(Next, <<businessState, lifecycleState>>)
fairness_assumptions ==
    \/ STSF_vars(Issue(v), v \in Vouchers, <<businessState, lifecycleState>>)
    \/ STSF_vars(Redeem(v) \/ Cancel(v), v \in Vouchers, <<businessState, lifecycleState>>)

END VoucherLifecycle
```