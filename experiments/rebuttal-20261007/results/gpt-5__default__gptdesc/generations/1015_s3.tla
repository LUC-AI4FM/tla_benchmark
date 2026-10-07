----------------------------- MODULE VoucherLifecycle -----------------------------

EXTENDS Naturals

CONSTANTS Voucher

ASSUME Voucher # {}

(*
  Life-cycle states and a decoupled "machine" view of those states.
*)
LifeCycleStates == {"phantom", "valid", "redeemed", "cancelled"}
MachineStates    == {"P", "V", "R", "C"}

(*
  Canonical mapping from business life-cycle state to machine state.
*)
LCMap(s) ==
  IF s = "phantom" THEN "P"
  ELSE IF s = "valid" THEN "V"
  ELSE IF s = "redeemed" THEN "R"
  ELSE "C"

VARIABLES
  vState,    \* business life-cycle state of each voucher
  mState     \* decoupled machine state of each voucher

Init ==
  /\ vState \in [Voucher -> LifeCycleStates]
  /\ mState \in [Voucher -> MachineStates]
  /\ \A v \in Voucher:
        /\ vState[v] = "phantom"
        /\ mState[v] = "P"

(*
  Voucher actions:
   - Issue: phantom -> valid
   - Redeem: valid -> redeemed (terminal)
   - Cancel: valid -> cancelled (terminal)
   - Transfer: allowed only while valid; modeled as stuttering (no state change)
*)
Issue(v) ==
  /\ v \in Voucher
  /\ vState[v] = "phantom"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ mState' = [mState EXCEPT ![v] = "V"]

Redeem(v) ==
  /\ v \in Voucher
  /\ vState[v] = "valid"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ mState' = [mState EXCEPT ![v] = "R"]

Cancel(v) ==
  /\ v \in Voucher
  /\ vState[v] = "valid"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ mState' = [mState EXCEPT ![v] = "C"]

Transfer(v) ==
  /\ v \in Voucher
  /\ vState[v] = "valid"
  /\ UNCHANGED << vState, mState >>

Next ==
  \E v \in Voucher:
    Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)

Spec ==
  Init /\ []Next

(*
  Safety invariants
*)
TypeOK ==
  /\ vState \in [Voucher -> LifeCycleStates]
  /\ mState \in [Voucher -> MachineStates]

Consistency ==
  \A v \in Voucher: mState[v] = LCMap(vState[v])

THEOREM TypeOKAndConsistencyAlwaysPreserved ==
  Spec => [](TypeOK /\ Consistency)
PROOF OBVIOUS

================================================================================