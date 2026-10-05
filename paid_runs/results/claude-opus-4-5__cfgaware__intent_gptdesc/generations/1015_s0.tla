---------------------------- MODULE voucher ----------------------------

EXTENDS Naturals

CONSTANTS V

VARIABLES vBusinessState, vLifecycleState

vars == <<vBusinessState, vLifecycleState>>

\* Business states
BusinessStates == {"not_yet_issued", "issued", "consumed", "cancelled"}

\* Lifecycle machine states
LifecycleStates == {"not_started", "active", "completed"}

\* Pick a specific voucher for potential use in configuration
v2 == CHOOSE x \in V : TRUE

\* Type invariant: all voucher states belong to allowed sets
VTypeOK ==
    /\ \A v \in V : vBusinessState[v] \in BusinessStates
    /\ \A v \in V : vLifecycleState[v] \in LifecycleStates

\* Consistency invariant: business state and lifecycle state must be consistent
VConsistent ==
    \A v \in V :
        /\ (vBusinessState[v] = "not_yet_issued") <=> (vLifecycleState[v] = "not_started")
        /\ (vBusinessState[v] = "issued") <=> (vLifecycleState[v] = "active")
        /\ (vBusinessState[v] \in {"consumed", "cancelled"}) <=> (vLifecycleState[v] = "completed")
        \* Only one terminal state when completed
        /\ (vLifecycleState[v] = "completed") => 
           ((vBusinessState[v] = "consumed") \/ (vBusinessState[v] = "cancelled"))
        /\ ~((vBusinessState[v] = "consumed") /\ (vBusinessState[v] = "cancelled"))

\* Initial state: all vouchers start unissued with lifecycle not started
VInit ==
    /\ vBusinessState = [v \in V |-> "not_yet_issued"]
    /\ vLifecycleState = [v \in V |-> "not_started"]

\* Issue action: move a not-yet-issued voucher to issued/active
Issue(v) ==
    /\ vBusinessState[v] = "not_yet_issued"
    /\ vLifecycleState[v] = "not_started"
    /\ vBusinessState' = [vBusinessState EXCEPT ![v] = "issued"]
    /\ vLifecycleState' = [vLifecycleState EXCEPT ![v] = "active"]

\* Transfer action: no-op while voucher is issued/active (state unchanged)
Transfer(v) ==
    /\ vBusinessState[v] = "issued"
    /\ vLifecycleState[v] = "active"
    /\ UNCHANGED vars

\* Redeem action: consume the voucher and complete its lifecycle
Redeem(v) ==
    /\ vBusinessState[v] = "issued"
    /\ vLifecycleState[v] = "active"
    /\ vBusinessState' = [vBusinessState EXCEPT ![v] = "consumed"]
    /\ vLifecycleState' = [vLifecycleState EXCEPT ![v] = "completed"]

\* Cancel action: invalidate the voucher and complete its lifecycle
Cancel(v) ==
    /\ vBusinessState[v] = "issued"
    /\ vLifecycleState[v] = "active"
    /\ vBusinessState' = [vBusinessState EXCEPT ![v] = "cancelled"]
    /\ vLifecycleState' = [vLifecycleState EXCEPT ![v] = "completed"]

\* Next state relation: any voucher can perform any enabled action
VNext ==
    \E v \in V :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

\* Complete specification with fairness
VSpec == VInit /\ [][VNext]_vars

\* Theorem: Type and consistency invariants are preserved
THEOREM VSpec => [](VTypeOK /\ VConsistent)

=============================================================================