---------------------------- MODULE VoucherLifecycle ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT V

VARIABLES vState, vlcState

vars == << vState, vlcState >>

\* Business states of a voucher
BusinessStates == {"dummy", "valid", "redeemed", "cancelled"}

\* Lifecycle-machine states
LifecycleStates == {"init", "working", "done"}

-----------------------------------------------------------------------------
\* Type invariant: every voucher's states belong to the allowed sets
VTypeOK ==
    /\ vState \in [V -> BusinessStates]
    /\ vlcState \in [V -> LifecycleStates]

\* Consistency invariant between business state and lifecycle state
VConsistent ==
    \A v \in V :
        /\ (vState[v] = "dummy")     <=> (vlcState[v] = "init")
        /\ (vState[v] = "valid")     <=> (vlcState[v] = "working")
        /\ (vlcState[v] = "done")    <=> (vState[v] \in {"redeemed", "cancelled"})
        /\ ~(vState[v] = "redeemed" /\ vState[v] = "cancelled")

-----------------------------------------------------------------------------
VInit ==
    /\ vState = [v \in V |-> "dummy"]
    /\ vlcState = [v \in V |-> "init"]

\* Issue a not-yet-issued voucher
Issue(v) ==
    /\ vState[v] = "dummy"
    /\ vlcState[v] = "init"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

\* Transfer (or other no-op) while issued/active
Transfer(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ UNCHANGED vars

\* Redeem: consume the voucher and complete its lifecycle
Redeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

\* Cancel: invalidate the voucher and complete its lifecycle
Cancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext ==
    \E v \in V :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

VSpec == VInit /\ [][VNext]_vars

-----------------------------------------------------------------------------
\* Additional properties

\* Once completed, a voucher stays in its terminal state and done lifecycle
TerminalStable ==
    \A v \in V :
        [][ (vlcState[v] = "done") =>
              /\ vlcState'[v] = "done"
              /\ vState'[v] = vState[v] ]_vars

\* Once issued, never reverts to not-yet-issued
NoRevert ==
    \A v \in V :
        [][ (vState[v] # "dummy") => (vState'[v] # "dummy") ]_vars

\* Issuing only from not-yet-issued; redeem/cancel only from issued/active
TransitionGuards ==
    \A v \in V :
        [][ /\ (vState[v] = "dummy" /\ vState'[v] = "valid")
                 => (vlcState[v] = "init")
            /\ (vState'[v] \in {"redeemed", "cancelled"} /\ vState[v] # vState'[v])
                 => (vState[v] = "valid" /\ vlcState[v] = "working") ]_vars

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=============================================================================